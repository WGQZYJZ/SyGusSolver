import sys
import sexp
import pprint
import translator

def Extend(Stmts,Productions):
    ret = []
    for i in range(len(Stmts)):
        if type(Stmts[i]) == list:
            TryExtend = Extend(Stmts[i],Productions)
            if len(TryExtend) > 0 :
                for extended in TryExtend:
                    ret.append(Stmts[0:i]+[extended]+Stmts[i+1:])
        elif type(Stmts[i]) == tuple:
            continue
        elif Stmts[i] in Productions:
            for extended in Productions[Stmts[i]]:
                ret.append(Stmts[0:i]+[extended]+Stmts[i+1:])
        if len(ret) > 0:
            break
    return ret

def solve(bmExpr):
    checker=translator.ReadQuery(bmExpr)
    SynFunExpr = []
    StartSym = 'My-Start-Symbol' 
    for expr in bmExpr:
        if len(expr)==0:
            continue
        elif expr[0]=='synth-fun':
            SynFunExpr=expr
    FuncDefine = ['define-fun']+SynFunExpr[1:4] 
    BfsQueue = [[StartSym]] 
    Productions = {StartSym:[]}
    Type = {StartSym:SynFunExpr[3]} 
    for NonTerm in SynFunExpr[4]: 
        NTName = NonTerm[0]
        NTType = NonTerm[1]
        if NTType == Type[StartSym]:
            Productions[StartSym].append(NTName)
        Type[NTName] = NTType
        Productions[NTName] = NonTerm[2]
    Count = 0
    TE_set = set()
    while(len(BfsQueue)!=0):
        Curr = BfsQueue.pop(0)
        TryExtend = Extend(Curr,Productions)
        if(len(TryExtend)==0): 
            FuncDefineStr = translator.toString(FuncDefine,ForceBracket = True) 
            CurrStr = translator.toString(Curr)
            Str = FuncDefineStr[:-1]+' '+ CurrStr+FuncDefineStr[-1] 
            Count += 1
            counterexample = checker.check(Str)
            if(counterexample == None): 
                Ans = Str
                break
        for TE in TryExtend:
            TE_str = str(TE)
            if not TE_str in TE_set:
                BfsQueue.append(TE)
                TE_set.add(TE_str)
    return Ans
   