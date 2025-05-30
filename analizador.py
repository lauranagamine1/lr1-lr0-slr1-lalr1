#!/usr/bin/env python3
import sys
from collections import defaultdict

EPSILON = 'ϵ'
ENDMARKER = '$'

def prompt_filepath():
    filepath = input("Ingresa la ruta del archivo de gramática (por ejemplo 'input.txt'): ")
    return filepath.strip()

class Grammar:
    def __init__(self, filepath):
        self.productions = defaultdict(list)
        self._parse_file(filepath)
        self.nonterminals = set(self.productions.keys())
        self.terminals = set()
        for rhss in self.productions.values():
            for rhs in rhss:
                for sym in rhs:
                    if sym != EPSILON and sym not in self.nonterminals:
                        self.terminals.add(sym)
        self.start_symbol = next(iter(self.productions))
        self.augmented_start = self.start_symbol + "'"
        self.productions[self.augmented_start] = [[self.start_symbol]]
        self.nonterminals.add(self.augmented_start)
        self.terminals.add(ENDMARKER)
        self.compute_first()
        self.compute_follow()

    def _parse_file(self, filepath):
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                for line in f:
                    line = line.strip()
                    if not line or line.startswith('#'):
                        continue
                    if '->' not in line:
                        raise ValueError(f"Línea inválida (no '->'): {line}")
                    lhs, rhs = line.split('->',1)
                    lhs = lhs.strip()
                    for prod in rhs.split('|'):
                        prod = prod.strip()
                        if not prod: continue
                        symbols = prod.split()
                        self.productions[lhs].append(symbols)
        except FileNotFoundError:
            raise FileNotFoundError(f"No se encontró el archivo: {filepath}")
        except Exception as e:
            raise RuntimeError(f"Error al leer gramática: {e}")

    def compute_first(self):
        self.first = defaultdict(set)
        for t in self.terminals:
            self.first[t].add(t)
        for A in self.nonterminals:
            self.first[A] = set()
        changed = True
        while changed:
            changed = False
            for A in self.nonterminals:
                for rhs in self.productions[A]:
                    before = len(self.first[A])
                    if rhs == [EPSILON]:
                        self.first[A].add(EPSILON)
                    else:
                        for sym in rhs:
                            self.first[A].update(x for x in self.first[sym] if x != EPSILON)
                            if EPSILON not in self.first[sym]: break
                        else:
                            self.first[A].add(EPSILON)
                    if len(self.first[A]) > before:
                        changed = True

    def compute_follow(self):
        self.follow = defaultdict(set)
        self.follow[self.augmented_start].add(ENDMARKER)
        changed = True
        while changed:
            changed = False
            for A in self.nonterminals:
                for rhs in self.productions[A]:
                    trailer = self.follow[A].copy()
                    for sym in reversed(rhs):
                        if sym in self.nonterminals:
                            before = len(self.follow[sym])
                            self.follow[sym].update(trailer)
                            if EPSILON in self.first[sym]:
                                trailer.update(x for x in self.first[sym] if x != EPSILON)
                            else:
                                trailer = self.first[sym].copy()
                            if len(self.follow[sym]) > before: changed = True
                        else:
                            trailer = self.first[sym].copy()

# AFN/AFD mejorados: estados numerados, inicial/finales claros
class NFA:
    def __init__(self):
        self.start = 0
        self.transitions = defaultdict(list)
        self.final_states = set()
        self.state_count = 1  # for unique state ids

    def add_production(self, rhs):
        prev = self.start
        if rhs == [EPSILON]:
            self.transitions[prev].append((EPSILON, prev))
            self.final_states.add(prev)
        else:
            for sym in rhs:
                nxt = self.state_count
                self.state_count += 1
                self.transitions[prev].append((sym, nxt))
                prev = nxt
            self.final_states.add(prev)

    def epsilon_closure(self, states):
        stack = list(states)
        res = set(states)
        while stack:
            p = stack.pop()
            for sym, q in self.transitions[p]:
                if sym == EPSILON and q not in res:
                    res.add(q)
                    stack.append(q)
        return res

def determinize_nfa(nfa, symbols):
    start = frozenset(nfa.epsilon_closure({nfa.start}))
    D = {start: {}}
    queue = [start]
    state_numbers = {start: 0}
    final_states = set()
    next_id = 1
    while queue:
        U = queue.pop(0)
        if any(u in nfa.final_states for u in U):
            final_states.add(state_numbers[U])
        for sym in symbols:
            if sym == EPSILON: continue
            moves = set()
            for p in U:
                for s, q in nfa.transitions[p]:
                    if s == sym:
                        moves.add(q)
            if not moves:
                continue
            V = frozenset(nfa.epsilon_closure(moves))
            if V not in D:
                D[V] = {}
                state_numbers[V] = next_id
                if any(u in nfa.final_states for u in V):
                    final_states.add(next_id)
                next_id += 1
                queue.append(V)
            D[U][sym] = V
    return D, state_numbers, final_states

def print_nfa(nfa):
    print("\n=== AFN ===")
    print(f"Estado inicial: {nfa.start}")
    print(f"Estados finales: {sorted(nfa.final_states)}")
    for p in sorted(nfa.transitions):
        for sym, q in nfa.transitions[p]:
            print(f" {p} --{sym}--> {q}")

def print_dfa(dfa, state_numbers, final_states):
    print("\n=== AFD ===")
    for U, trans in dfa.items():
        st = state_numbers[U]
        tipo = []
        if st == 0: tipo.append("inicial")
        if st in final_states: tipo.append("final")
        tipo_txt = " ("+", ".join(tipo)+")" if tipo else ""
        print(f"Estado {st}{tipo_txt}: {sorted(U)}")
        for sym, V in trans.items():
            print(f"  --{sym}--> Estado {state_numbers[V]}")

# ... (El resto del código LR/SLR/LALR/LR1 y print_table igual que tu versión previa, sin cambios) ...
# Inclúyelo igual después de aquí ↓

# Objetos para LR(0)
class LR0Item:
    def __init__(self,lhs,rhs,dot=0):
        self.lhs,self.rhs,self.dot = lhs,rhs,dot
    def next_symbol(self): return None if self.dot>=len(self.rhs) else self.rhs[self.dot]
    def is_reduce(self): return self.dot==len(self.rhs)
    def core(self): return (self.lhs,tuple(self.rhs),self.dot)
    def __eq__(self,other): return self.core()==other.core()
    def __hash__(self): return hash(self.core())
    def __repr__(self): return f"{self.lhs} -> {' '.join(self.rhs[:self.dot])} • {' '.join(self.rhs[self.dot:])}"

def closure0(items, grammar):
    C=set(items); added=True
    while added:
        added=False
        for it in list(C):
            sym=it.next_symbol()
            if sym in grammar.nonterminals:
                for rhs in grammar.productions[sym]:
                    new=LR0Item(sym,rhs,0)
                    if new not in C: C.add(new); added=True
    return C

def goto0(items,sym,grammar):
    return closure0([LR0Item(it.lhs,it.rhs,it.dot+1) for it in items if it.next_symbol()==sym],grammar)

def canonical_collection0(grammar):
    start = LR0Item(grammar.augmented_start, grammar.productions[grammar.augmented_start][0],0)
    C=[closure0({start},grammar)]
    changed=True
    while changed:
        changed=False
        for I in list(C):
            for sym in grammar.nonterminals|grammar.terminals:
                J=goto0(I,sym,grammar)
                if J and J not in C: C.append(J); changed=True
    return C

def build_table_LR0(grammar,C):
    action=defaultdict(dict); goto_tbl=defaultdict(dict)
    # Enumerar producciones
    prods=[]; pid={}
    for A,rhss in grammar.productions.items():
        for rhs in rhss:
            pid[(A,tuple(rhs))]=len(prods); prods.append((A,rhs))
    for i,I in enumerate(C):
        for it in I:
            a=it.next_symbol()
            if a in grammar.terminals:
                j=C.index(goto0(I,a,grammar)); action[i][a]=('s',j)
            if it.is_reduce():
                if it.lhs==grammar.augmented_start: action[i][ENDMARKER]=('acc',)
                else:
                    idx=pid[(it.lhs,tuple(it.rhs))]
                    for t in grammar.follow[it.lhs]: action[i][t]=('r',idx)
        for A in grammar.nonterminals:
            j=C.index(goto0(I,A,grammar)) if goto0(I,A,grammar) else None
            if j is not None: goto_tbl[i][A]=j
    return action,goto_tbl,prods

# Objetos para LR(1)
class LR1Item(LR0Item):
    def __init__(self,lhs,rhs,dot,lookahead):
        super().__init__(lhs,rhs,dot); self.lookahead=lookahead
    def core(self): return (self.lhs,tuple(self.rhs),self.dot)
    def __eq__(self,other): return (self.core(),self.lookahead)==(other.core(),other.lookahead)
    def __hash__(self): return hash((self.core(),self.lookahead))
    def __repr__(self): return f"{self.lhs} -> {' '.join(self.rhs[:self.dot])} • {' '.join(self.rhs[self.dot:])}, {self.lookahead}"

def closure1(items,grammar):
    C=set(items); added=True
    while added:
        added=False
        for it in list(C):
            B=it.next_symbol()
            if B in grammar.nonterminals:
                beta=it.rhs[it.dot+1:]
                for rhs in grammar.productions[B]:
                    for look in compute_lookaheads(grammar,beta,it.lookahead):
                        new=LR1Item(B,rhs,0,look)
                        if new not in C: C.add(new); added=True
    return C

def compute_lookaheads(grammar,beta,a):
    first_beta_a=set(); seq=beta+[a]
    for sym in seq:
        first_beta_a.update(x for x in grammar.first[sym] if x!=EPSILON)
        if EPSILON not in grammar.first[sym]: break
    return first_beta_a

def goto1(items,sym,grammar):
    return closure1([LR1Item(it.lhs,it.rhs,it.dot+1,it.lookahead) for it in items if it.next_symbol()==sym],grammar)

def canonical_collection1(grammar):
    start=LR1Item(grammar.augmented_start,grammar.productions[grammar.augmented_start][0],0,ENDMARKER)
    C=[closure1({start},grammar)]; changed=True
    while changed:
        changed=False
        for I in list(C):
            for sym in grammar.nonterminals|grammar.terminals:
                J=goto1(I,sym,grammar)
                if J and J not in C: C.append(J); changed=True
    return C

def build_table_LR1(grammar,C):
    action=defaultdict(dict); goto_tbl=defaultdict(dict)
    prods=[]; pid={}
    for A,rhss in grammar.productions.items():
        for rhs in rhss:
            pid[(A,tuple(rhs))]=len(prods); prods.append((A,rhs))
    for i,I in enumerate(C):
        for it in I:
            a=it.next_symbol()
            if a in grammar.terminals:
                j=C.index(goto1(I,a,grammar)); action[i][a]=('s',j)
            if it.is_reduce():
                if it.lhs==grammar.augmented_start: action[i][ENDMARKER]=('acc',)
                else: action[i][it.lookahead]=('r',pid[(it.lhs,tuple(it.rhs))])
        for A in grammar.nonterminals:
            J=goto1(I,A,grammar)
            if J: goto_tbl[i][A]=C.index(J)
    return action,goto_tbl,prods

from collections import OrderedDict
def merge_LR1_to_LALR(C1):
    core_map=OrderedDict()
    for i,I in enumerate(C1):
        core=frozenset(it.core() for it in I)
        core_map.setdefault(core,[]).append(i)
    C2=[]; state_map={}
    for new_id,(core,idxs) in enumerate(core_map.items()):
        merged=set()
        for i in idxs: merged |= C1[i]
        C2.append(merged)
        for i in idxs: state_map[i]=new_id
    return C2

def print_table(action,goto_tbl,prods):
    print("\n=== Tabla de análisis ===")
    symbols = sorted(set(sym for row in action.values() for sym in row) | set(A for row in goto_tbl.values() for A in row))
    header=["state"]+symbols
    print(' | '.join(f"{h:^10}" for h in header))
    for i in range(max(action.keys()|goto_tbl.keys())+1):
        row=[str(i)]
        for sym in symbols:
            cell=''
            if sym in action[i]:
                act=action[i][sym]
                cell='acc' if act[0]=='acc' else f"{act[0]}{act[1]}"
            elif sym in goto_tbl[i]: cell=str(goto_tbl[i][sym])
            row.append(cell)
        print(' | '.join(f"{c:^10}" for c in row))
    print("\nProducciones:")
    for idx,(A,rhs) in enumerate(prods): print(f" {idx}: {A} -> {' '.join(rhs)}")

def main():
    if len(sys.argv)>=2 and sys.argv[1] != '--test': filepath=sys.argv[1]
    else: filepath=prompt_filepath()
    try:
        grammar=Grammar(filepath)
    except Exception as e:
        print(e); sys.exit(1)
    print(f"Gramática cargada desde '{filepath}'.")
    nfa = NFA()
    for rhss in grammar.productions.values():
        for rhs in rhss:
            nfa.add_production(rhs)
    print_nfa(nfa)
    dfa, state_numbers, final_states = determinize_nfa(nfa, grammar.terminals)
    print_dfa(dfa, state_numbers, final_states)
    print("\nSelecciona análisis: 1) LR0 2) SLR1 3) LALR1 4) LR1")
    choice=input("Opción [1-4]: ")
    if choice=='1':
        C0=canonical_collection0(grammar)
        A,G,P=build_table_LR0(grammar,C0)
        print_table(A,G,P)
    elif choice=='2':
        C0=canonical_collection0(grammar)
        A,G,P=build_table_LR0(grammar,C0)
        print_table(A,G,P)
    elif choice=='3':
        C1=canonical_collection1(grammar)
        C2=merge_LR1_to_LALR(C1)
        A,G,P=build_table_LR1(grammar,C2)
        print_table(A,G,P)
    elif choice=='4':
        C1=canonical_collection1(grammar)
        A,G,P=build_table_LR1(grammar,C1)
        print_table(A,G,P)
    else:
        print("Opción inválida.")

# Tests
import unittest
class TestGrammarParsing(unittest.TestCase):
    def setUp(self):
        self.test_file='test_gram.txt'
        with open(self.test_file,'w',encoding='utf-8') as f:
            f.write('S -> a S | b | ϵ')
        self.grammar=Grammar(self.test_file)
    def tearDown(self):
        import os; os.remove(self.test_file)
    def test_productions(self):
        self.assertIn('S',self.grammar.productions)
        self.assertIn([EPSILON],self.grammar.productions['S'])
    def test_first(self):
        self.assertIn(EPSILON,self.grammar.first['S'])
if __name__=='__main__':
    if '--test' in sys.argv:
        sys.argv.remove('--test'); unittest.main()
    else:
        main()
