"""
ctlmc.py -- helpers for the explicit-state CTL model checking exercise
(Introduction to Software Verification, 2360342, Lecture 3/4).

What is in here (all of it is *given* to the students):
  * Kripke structures as igraph graphs          -> microwave(), toy_model()
  * a small CTL parser                          -> parse()
  * rewriting into the basis  {not, and, or, EX, EU, EG}   -> normalize()
  * the formula as a graph (a DAG of sub-formulas)          -> formula_graph()
  * printing / drawing                          -> draw_model(), draw_formula(), show(), ...
  * SCC helper (Tarjan, via igraph)             -> nontrivial_sccs()
  * fair EG for the fairness part               -> fair_EG()

Switches:  TRACE (print the steps)  and  DRAW (draw the steps) -- see settings().
"""
import re
import igraph as ig
import matplotlib.pyplot as plt
plt.rcParams['figure.dpi'] = 110
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch, Circle, Arc

# ----------------------------------------------------------------------------- settings
TRACE = True          # print every step of the procedures
DRAW = True           # draw the model at every step of the procedures
DRAW_SUMMARY = True   # after each sub-formula: draw formula graph + model side by side

def settings(trace=None, draw=None, summary=None):
    """Turn printing / drawing on and off, e.g. settings(draw=False)."""
    global TRACE, DRAW, DRAW_SUMMARY
    if trace is not None: TRACE = trace
    if draw is not None: DRAW = draw
    if summary is not None: DRAW_SUMMARY = summary

MAR, GRN, LGRN, INK, GREY, TINT, GTINT, BORDER = '#5D2E46', '#2E8B57', '#44AF77', '#222222', '#6B6B6B', '#F4EEF1', '#E8F4EC', '#CFC9B4'

# ----------------------------------------------------------------------------- models
def kripke(n, edges, props, init, pos=None, actions=None, title='M'):
    """Build a Kripke structure: states 0..n-1, transitions, labeling L(s), initial states."""
    M = ig.Graph(n, edges, directed=True)
    M['title'] = title
    M['init'] = set(init)
    M.vs['id'] = list(range(n))
    M.vs['props'] = [set(p) for p in props]
    M.vs['plist'] = [list(p) for p in props]          # display order
    M.vs['pos'] = pos if pos is not None else [tuple(c) for c in M.layout_auto().coords]
    M.es['action'] = actions if actions is not None else [''] * len(edges)
    return M

def microwave():
    """The microwave example from the lecture (states numbered 0..6 here, 1..7 on the slides)."""
    edges = [(0, 1), (0, 2), (1, 4), (2, 0), (2, 5), (3, 3), (3, 0), (3, 2), (4, 1), (4, 2), (5, 6), (6, 3)]
    actions = ['start', 'close', 'close', 'open', 'start', 'cook', 'open', 'done', 'open', 'reset', 'warmup', 'start']
    props = [[], ['Start', 'Error'], ['Close'], ['Close', 'Heat'], ['Start', 'Close', 'Error'],
             ['Start', 'Close'], ['Start', 'Close', 'Heat']]
    pos = [(0, 0), (-2, 1.6), (0, 1.6), (2, 1.6), (-2, 3.2), (0, 3.2), (2, 3.2)]
    return kripke(7, edges, props, init=[0], pos=pos, actions=actions, title='Microwave')

def toy_model():
    """A small 4-state model, used to show the algorithm with AP, not, and, EX only."""
    edges = [(0, 1), (1, 2), (2, 0), (2, 3), (3, 3)]
    props = [['p'], ['q'], ['p', 'q'], []]
    pos = [(0, 0), (2, 0), (2, 1.8), (0, 1.8)]
    return kripke(4, edges, props, init=[0], pos=pos, title='Toy model')

def states(M):
    return set(range(M.vcount()))

# ----------------------------------------------------------------------------- formulas
# AST: ('AP', name) | ('true',) | ('not', f) | ('and', f, g) | ('or', f, g) | ('->', f, g)
#      ('EX', f) | ('EG', f) | ('EF', f) | ('AX', f) | ('AG', f) | ('AF', f) | ('EU', f, g) | ('AU', f, g)
_TOK = re.compile(r'\s*(->|[()\[\]!&|~]|[A-Za-z_][A-Za-z0-9_]*)')

def _tokens(s):
    s = s.strip(); out = []; i = 0
    while i < len(s):
        m = _TOK.match(s, i)
        if not m: raise SyntaxError(f'cannot parse at: {s[i:]!r}')
        out.append(m.group(1)); i = m.end()
    return out

def parse(s):
    """Parse a CTL formula, e.g. 'AG(Start -> AF Heat)' or '!E(true U (Start & EG !Heat))'.
    Operators: ! (not), &, |, ->, EX EF EG AX AF AG, E(f U g), A(f U g); constants true, false."""
    toks = _tokens(s); pos = [0]
    def peek(): return toks[pos[0]] if pos[0] < len(toks) else None
    def take(t=None):
        tok = peek()
        if t is not None and tok != t: raise SyntaxError(f'expected {t!r} but found {tok!r}')
        pos[0] += 1; return tok
    def imp():
        a = disj()
        if peek() == '->': take(); return ('->', a, imp())
        return a
    def disj():
        a = conj()
        while peek() == '|': take(); a = ('or', a, conj())
        return a
    def conj():
        a = unary()
        while peek() == '&': take(); a = ('and', a, unary())
        return a
    def unary():
        t = peek()
        if t in ('!', '~'): take(); return ('not', unary())
        if t in ('EX', 'EF', 'EG', 'AX', 'AF', 'AG'): take(); return (t, unary())
        if t in ('E', 'A') and pos[0] + 1 < len(toks) and toks[pos[0] + 1] in ('(', '['):
            q = take(); close = ')' if take() == '(' else ']'
            a = imp(); take('U'); b = imp(); take(close)
            return ('EU' if q == 'E' else 'AU', a, b)
        if t in ('(', '['):
            close = ')' if take() == '(' else ']'; a = imp(); take(close); return a
        if t == 'true': take(); return ('true',)
        if t == 'false': take(); return ('not', ('true',))
        if t is None or not re.match(r'[A-Za-z_]', t): raise SyntaxError(f'unexpected {t!r}')
        return ('AP', take())
    f = imp()
    if peek() is not None: raise SyntaxError(f'unexpected {peek()!r}')
    return f

def normalize(f):
    """Rewrite into the basis {AP, true, not, and, or, EX, EU, EG} (the 'Expressiveness' slide)."""
    op = f[0]
    if op in ('AP', 'true'): return f
    a = [normalize(x) for x in f[1:]]
    def NOT(x): return x[1] if x[0] == 'not' else ('not', x)      # remove double negation
    if op == 'not': return NOT(a[0])
    if op in ('and', 'or', 'EX', 'EG', 'EU'): return (op, *a)
    if op == '->': return NOT(('and', a[0], NOT(a[1])))          # f -> g  =  !(f & !g)
    if op == 'EF': return ('EU', ('true',), a[0])
    if op == 'AX': return NOT(('EX', NOT(a[0])))
    if op == 'AG': return NOT(('EU', ('true',), NOT(a[0])))
    if op == 'AF': return NOT(('EG', NOT(a[0])))
    if op == 'AU':  # A[f U g] = !EG !g & !E[!g U (!f & !g)]
        f1, g1 = a
        return ('and', NOT(('EG', NOT(g1))), NOT(('EU', NOT(g1), ('and', NOT(f1), NOT(g1)))))
    raise ValueError(op)

_SYM = {'not': '!', 'and': '&', 'or': '|', '->': '->'}
def to_str(f, top=True):
    """Pretty-print a formula (AST)."""
    op = f[0]
    if op == 'AP': return f[1]
    if op == 'true': return 'true'
    if op == 'not':
        s = to_str(f[1], False)
        return '!' + s
    if op in ('EX', 'EG', 'EF', 'AX', 'AG', 'AF'): return op + ' ' + to_str(f[1], False)
    if op in ('EU', 'AU'): return f'{op[0]}({to_str(f[1], False)} U {to_str(f[2], False)})'
    s = f'{to_str(f[1], False)} {_SYM[op]} {to_str(f[2], False)}'
    return s if top else f'({s})'

def formula_graph(f):
    """The formula as a graph: one vertex per *distinct* sub-formula (a DAG),
    an edge from every sub-formula to its operands.
    Vertex attributes:  op, label (the sub-formula as a string), ap (for AP), children (ordered list).
    Graph attribute:    root."""
    if isinstance(f, str): f = normalize(parse(f))
    F = ig.Graph(directed=True); index = {}
    def add(g):
        key = to_str(g)
        if key in index: return index[key]          # shared sub-formula -> same vertex
        kids = [add(c) for c in g[1:]] if g[0] not in ('AP', 'true') else []
        v = F.add_vertex(op=g[0], label=key, ap=(g[1] if g[0] == 'AP' else None), children=kids).index
        index[key] = v
        for c in kids: F.add_edge(v, c)
        return v
    F['root'] = add(f)
    F['formula'] = to_str(f)
    return F

# ----------------------------------------------------------------------------- printing
def log(*a):
    if TRACE: print(*a)

def fmt(S):
    return '{' + ', '.join(str(x) for x in sorted(S)) + '}'

# ----------------------------------------------------------------------------- drawing: model
def _arrow(ax, p, q, rad=0.0, color=INK, lw=1.2, r=0.36, rq=None):
    """Arrow from circle at p to circle at q (radii r, rq), trimmed in data coordinates."""
    rq = r if rq is None else rq
    dx, dy = q[0] - p[0], q[1] - p[1]; L = max((dx * dx + dy * dy) ** 0.5, 1e-9)
    a = (p[0] + dx / L * r, p[1] + dy / L * r); b = (q[0] - dx / L * rq, q[1] - dy / L * rq)
    ax.add_patch(FancyArrowPatch(a, b, connectionstyle=f'arc3,rad={rad}', arrowstyle='-|>', mutation_scale=12,
                                 shrinkA=0, shrinkB=0, color=color, lw=lw, zorder=1))

def draw_model(M, labeled=(), frontier=(), current=None, title=None, ax=None, show_actions=True):
    """Draw the Kripke structure.
       labeled  -- states in the set computed so far   (maroon)
       frontier -- states currently in the work list T (green ring)
       current  -- the state being processed           (thick green border)"""
    own = ax is None
    if own: fig, ax = plt.subplots(figsize=(6.2, 4.6))
    labeled, frontier = set(labeled), set(frontier)
    P = [(x, -y) for x, y in M.vs['pos']]
    pairs = {(e.source, e.target) for e in M.es}
    R = 0.42
    for e in M.es:
        s, t = e.source, e.target
        if s == t:   # self loop
            x, y = P[s]
            ax.add_patch(Arc((x + 0.36, y + 0.36), 0.42, 0.42, theta1=-120, theta2=200, color=INK, lw=1.2))
            if show_actions and e['action']: ax.text(x + 0.62, y + 0.62, e['action'], fontsize=8, color=GREY)
            continue
        rad = 0.18 if (t, s) in pairs else 0.0
        _arrow(ax, P[s], P[t], rad=rad, r=R)
        if show_actions and e['action']:
            mx, my = (P[s][0] + P[t][0]) / 2, (P[s][1] + P[t][1]) / 2
            dx, dy = P[t][1] - P[s][1], -(P[t][0] - P[s][0]); L = max((dx * dx + dy * dy) ** 0.5, 1e-9)
            off = 0.18 + (0.12 if rad else 0)
            ax.text(mx + dx / L * off, my + dy / L * off, e['action'], fontsize=8, color=GREY, ha='center', va='center')
    for v in M.vs:
        x, y = P[v.index]
        lab = v.index in labeled
        face = MAR if lab else 'white'
        edge = GRN if (v.index in frontier or v.index == current) else MAR
        lw = 3.2 if v.index == current else (2.4 if v.index in frontier else 1.2)
        ax.add_patch(Circle((x, y), R, facecolor=face, edgecolor=edge, lw=lw, zorder=2))
        col = 'white' if lab else INK
        ax.text(x, y + 0.22, str(v.index), ha='center', va='center', fontsize=10, fontweight='bold', color=col, zorder=3)
        ax.text(x, y - 0.07, '\n'.join(v['plist']), ha='center', va='center', fontsize=6, color=col, zorder=3,
                linespacing=0.95)
        if v.index in M['init']:
            _arrow(ax, (x - 0.8, y + 0.6), (x, y), color=GRN, r=0.0, rq=R)
    xs = [p[0] for p in P]; ys = [p[1] for p in P]
    ax.set_xlim(min(xs) - 1.0, max(xs) + 1.0); ax.set_ylim(min(ys) - 0.8, max(ys) + 0.9)
    ax.set_aspect('equal'); ax.axis('off')
    if title: ax.set_title(title, fontsize=11, color=MAR, loc='left')
    if own: plt.show()

def show(M, labeled=(), frontier=(), current=None, msg=''):
    """Print a step and (if DRAW) draw the model. Use it inside the MC procedures."""
    log(f'    {msg}   labeled={fmt(labeled)}   T={fmt(frontier)}')
    if DRAW:
        draw_model(M, labeled, frontier, current, title=msg)

# ----------------------------------------------------------------------------- drawing: formula graph
_OPSYM = {'not': '¬', 'and': '∧', 'or': '∨', 'true': 'true', 'EX': 'EX', 'EU': 'EU', 'EG': 'EG'}

def _layout(F, dx=1.7, dy=1.15):
    """Tree-like layout of the formula DAG: y = longest distance from the root,
    leaves get consecutive x slots (left to right), a parent is centred above its children."""
    depth = {}
    def d(v, k):
        if depth.get(v, -1) >= k: return
        depth[v] = k
        for c in F.vs[v]['children']: d(c, k + 1)
    d(F['root'], 0)
    x, slot = {}, [0]
    def place(v):
        if v in x: return
        ch = F.vs[v]['children']
        shared = [c in x for c in ch]                   # operands already placed by another parent
        for c in ch: place(c)
        if ch and not all(shared): x[v] = sum(x[c] for c in ch) / len(ch)
        else: x[v] = slot[0]; slot[0] += 1              # a leaf, or only shared operands: own column
    place(F['root'])
    # separate vertices that ended up too close on the same level
    levels = {}
    for v in x: levels.setdefault(depth[v], []).append(v)
    for vs in levels.values():
        vs.sort(key=lambda v: x[v])
        for a, b in zip(vs, vs[1:]):
            if x[b] - x[a] < 1: x[b] = x[a] + 1
    return {v: (x[v] * dx, -depth[v] * dy) for v in x}

def draw_formula(F, done=(), current=None, ax=None, full=True, title=None):
    """Draw the formula graph.  done = processed sub-formulas (maroon), current = the one being processed."""
    own = ax is None
    pos = _layout(F, dx=2.6 if full else 1.7); done = set(done)
    if own:
        xs = [p[0] for p in pos.values()]; ys = [p[1] for p in pos.values()]
        w = (max(xs) - min(xs)) + (5.5 if full else 3.2); h = (max(ys) - min(ys)) + 1.6
        s = min(1.05, 11 / w, 7 / h)
        fig, ax = plt.subplots(figsize=(max(w * s, 4), max(h * s, 2.5)))
    for v in F.vs:
        for i, c in enumerate(v['children']):
            p, q = pos[v.index], pos[c]
            dx, dy = q[0] - p[0], q[1] - p[1]
            k = min(0.64 / abs(dx) if dx else 1e9, 0.28 / abs(dy) if dy else 1e9)   # leave the box (half sizes 0.62 x 0.26)
            a, b = (p[0] + dx * k, p[1] + dy * k), (q[0] - dx * k, q[1] - dy * k)
            ax.add_patch(FancyArrowPatch(a, b, arrowstyle='-|>', mutation_scale=11, shrinkA=0, shrinkB=0, color=GREY, lw=1.1, zorder=1))
            if v['op'] == 'EU':
                ax.text((p[0] + q[0]) / 2, (p[1] + q[1]) / 2, str(i + 1), fontsize=8, color=GREY, ha='center')
    for v in F.vs:
        x, y = pos[v.index]
        txt = v['ap'] if v['op'] == 'AP' else _OPSYM[v['op']]
        is_done = v.index in done; is_cur = v.index == current
        face = MAR if is_done else (GTINT if v['op'] in ('AP', 'true') else 'white')
        ax.add_patch(FancyBboxPatch((x - 0.62, y - 0.26), 1.24, 0.52, boxstyle='round,pad=0.02,rounding_size=0.12',
                                    facecolor=face, edgecolor=GRN if is_cur else MAR, lw=3 if is_cur else 1.2, zorder=2))
        ax.text(x, y, txt, ha='center', va='center', fontsize=11, fontweight='bold', color='white' if is_done else MAR, zorder=3)
        if full:
            ax.text(x + 0.7, y, v['label'], ha='left', va='center', fontsize=7.5, color=GREY, zorder=3)
    xs = [p[0] for p in pos.values()]; ys = [p[1] for p in pos.values()]
    ax.set_xlim(min(xs) - 1.0, max(xs) + (4.5 if full else 1.0)); ax.set_ylim(min(ys) - 0.6, max(ys) + 0.6)
    ax.set_aspect('equal'); ax.axis('off')
    ax.set_title(title or F['formula'], fontsize=11, color=MAR, loc='left')
    if own: plt.show()

def draw_step(M, F, v, sat):
    """Formula graph (left) and the model with [[sub-formula]] (right)."""
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(12.5, 4.6), gridspec_kw={'width_ratios': [1, 1.05]})
    draw_formula(F, done=sat.keys(), current=v, ax=a1, full=False, title='formula graph')
    draw_model(M, labeled=sat[v], ax=a2, title=f"[[ {F.vs[v]['label']} ]] = {fmt(sat[v])}")
    plt.tight_layout(); plt.show()

# ----------------------------------------------------------------------------- SCCs and fairness
def nontrivial_sccs(M, S):
    """The nontrivial maximal SCCs of the model restricted to the states in S (Tarjan, via igraph).
    Returns a list of sets of states.  An SCC is nontrivial if it contains at least one edge."""
    S = sorted(S)
    if not S: return []
    sub = M.induced_subgraph(S)
    out = []
    for comp in sub.connected_components(mode='strong'):
        C = {S[i] for i in comp}
        if len(C) > 1 or any(M.are_adjacent(s, s) for s in C):
            out.append(C)
    return out

def fair_EG(M, S1, fairness):
    """[[E_F G f1]] given S1 = [[f1]] and a list of fairness sets P_i (Lecture 4):
    a state satisfies it iff it has a path inside S1 to a nontrivial *fair* MSCC of M restricted to S1
    (an SCC C is fair iff C ∩ P ≠ ∅ for every P ∈ F)."""
    S1 = set(S1)
    sccs = nontrivial_sccs(M, S1)
    fair = [C for C in sccs if all(C & set(P) for P in fairness)]
    log(f'    MSCCs of M\' = {[fmt(C) for C in sccs]}   fair ones: {[fmt(C) for C in fair]}')
    label = set().union(*fair) if fair else set()
    T = list(label)
    show(M, label, T, msg='E_F G: start from the fair MSCCs')
    while T:
        s = T.pop()
        for t in M.predecessors(s):
            if t in S1 and t not in label:
                label.add(t); T.append(t)
                show(M, label, T, current=t, msg=f'E_F G: {t} -> {s}, label {t}')
    return label
