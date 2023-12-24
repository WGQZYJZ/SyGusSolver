import sys
import sexp
import pprint
import translator
import bv, lib, myfallback

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

def stripComments(bmFile):
    noComments = '(\n'
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + '\n)'

if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0] #Parse string to python list
    '''
    checker=translator.ReadQuery(bmExpr)
    SynFunExpr = []
    StartSym = 'My-Start-Symbol' #virtual starting symbol
    for expr in bmExpr:
        if len(expr)==0:
            continue
        elif expr[0]=='synth-fun':
            SynFunExpr=expr
    FuncDefine = ['define-fun']+SynFunExpr[1:4] #copy function signature
    BfsQueue = [[StartSym]] #Top-down
    Productions = {StartSym:[]}
    Type = {StartSym:SynFunExpr[3]} # set starting symbol's return type
    for NonTerm in SynFunExpr[4]: #SynFunExpr[4] is the production rules
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
        #print("extend", Curr)
        TryExtend = Extend(Curr,Productions)
        if(len(TryExtend)==0): # Nothing to
            FuncDefineStr = translator.toString(FuncDefine,ForceBracket = True) # use Force Bracket = True on function definition. MAGIC CODE. DO NOT MODIFY THE ARGUMENT ForceBracket = True.
            CurrStr = translator.toString(Curr)
            Str = FuncDefineStr[:-1]+' '+ CurrStr+FuncDefineStr[-1] # insert Program just before the last bracket ')'
            Count += 1
            counterexample = checker.check(Str)
            if(counterexample == None): # No counter-example
                Ans = Str
                break
        for TE in TryExtend:
            TE_str = str(TE)
            if not TE_str in TE_set:
                BfsQueue.append(TE)
                TE_set.add(TE_str)
    '''
    Type = None
    for expr in bmExpr:
        if type(expr) is list:
            if expr[0] == 'set-logic':
                Type = expr[1]
                break
    ans = None
    if Type == 'BV' or Type == 'LIA':
        try:
            if Type == 'BV':
                ans = bv.solve(bmExpr)
                
            else:
                ans = lib.genAnswer(bmExpr)
        except Exception:
            ans = myfallback.solve(bmExpr)
        finally:
            with open('result.txt', 'w') as f:
                f.write(ans)
            exit(0)
    else:
        ans = myfallback.solve(bmExpr)
        with open('result.txt', 'w') as f:
            f.write(ans)

    '''
    print(Ans)
    with open('result.txt', 'w') as f:
        f.write(Ans)
    '''