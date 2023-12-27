import sys
import sexp
import pprint
import translator
import bv, fallback, lia

def stripComments(bmFile):
    noComments = '(\n'
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + '\n)'

if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0] 
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
                ans = bv.bvsolver(bmExpr, 8, 100)
            else:
                ans = lia.solve(bmExpr)
        except Exception:
            ans = fallback.solve(bmExpr)
        finally:
            with open('result.txt', 'w') as f:
                f.write(ans)
            exit(0)
    else:
        ans = fallback.solve(bmExpr)
        with open('result.txt', 'w') as f:
            f.write(ans)