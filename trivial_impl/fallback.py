import sys
import sexp
import pprint
import translator

tot = 0 #生成的表达式数量
synFunExpr = [] #定义函数的表达式列表
synFunName = '' #定义函数的名称
synFunName2Num = {} #定义函数中每个参数对应的名称编号
startSym = 'My-Start-Symbol' #开始符号
prodRules = {startSym: []} #开始符号下所有规则
retType = {} #开始符号对应的返回类型
depFunExpr = {startSym: [[] for i in range(100)]} #开始符号下所有依赖表达式列表
listAllFunExpr = [] #所有定义函数的表达式列表

class FunExpr:
    def __init__(self, term, expr, leng):
        super().__init__()
        self.term = term
        self.expr = expr
        self.leng = leng
        self.lExp = len(str(expr))

def stripComments(bmFile):
    noComments = "(\n"
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + "\n)"

# 定义一个名为parseRule的函数，它接受一个表达式作为参数，并返回一个元组，包含三个元素：
# 第一个元素是表达式本身，第二个元素是一个列表，存存储了所有匹配的规则，
# 第三个元素是一个函数，可以根据索引和规则列表生成对应的表达式。
def parseRule(expr):
    idx, idy = 0, 0
    listT = []

    # g接受一个表达式作为参数，并返回一个匿名函数。匿名函数的作用是将表达式分解为两部分：第一部分是列表或元组，第二部分是规则。
    # 如果参数是列表或元组，则匿名函数会递归地对其进行解析，并将结果存存储在listT中。
    # 如果参数是规则，则匿名函数会直接返回该规则。
    # 如果参数不是列表或元组也不是规则，则匿名函数会返回原始参数。
    def g(e):
        if type(e) == list:
            ret = [g(w) for w in e[1:]]
            return lambda *a: e[:1] + [gg(*a) for gg in ret]
        elif type(e) == tuple:
            return lambda *a: e
        elif e in prodRules:
            nonlocal idy
            idy += 1
            listT.append(e)
            return lambda *a, i=idy - 1: a[i]
        else:
            return lambda *a: e

    s = (expr, listT, g(expr)) # 创建一个新的元组，并将expr, listT, g作为其值
    return s

# 接受一个表达式作为参数，并返回一个字符串
def synFun2Def(expr):
    global synFunExpr
    return ['define-fun'] + synFunExpr[1:4] + [expr]

def genDepExpr(term, dep):
    # 遍历prodRules中term对应的列表，对每个列表中的元素进行处理。每个元素是一个元组(expr, listT, exprF)，
    # 其中expr是一个表达式，listT是一个列表，存存储了该表达式中所有可能的操作数（0或1），
    # exprF是一个匿名函数，用来生成该表达式对应的函数调用语句。
    for expr, listT, exprF in prodRules[term]:
        numT = len(listT) # 该表达式中操作数的个数
        listFE = [None] * numT # 该表达式中所有可能操作数（0或1）所占用的空间大小

        # 根据idx和leng来判断是否需要继续遍历下一个元素或者返回结果
        def dfsExpr(idx, leng):
            global tot
            tot += 1
            if idx == numT: # 已经遍历完所有元素
                if leng != dep:
                    return
                if type(expr) == list and numT == 2 and len(expr) == 3:
                    if (
                        expr[0] == 'and'
                        or expr[0] == 'or'
                        or expr[0] == '+'
                        or expr[0] == '*'
                        or expr[0] == '='
                    ) and listFE[0].lExp > listFE[1].lExp:
                        return

                newExpr = exprF(*[w.expr for w in listFE])
                fe = FunExpr(term, newExpr, dep)
                depFunExpr[term][dep].append(fe)
            else:
                dn = 1
                up = dep - leng - (numT - (idx + 1))
                if up < dn:
                    return
                if idx == numT - 1:
                    dn = up
                for cur in range(dn, up + 1):
                    for ef in depFunExpr[listT[idx]][cur]:
                        listFE[idx] = ef
                        dfsExpr(idx + 1, leng + cur)

        dfsExpr(0, 1)

def outpExpr(expr):
    fullExpr = synFun2Def(expr)
    strExpr = translator.toString(fullExpr, ForceBracket=True)
    return strExpr
    
def solve(bmExpr):
    global tot, synFunExpr, synFunName, synFunName2Num, startSym, prodRules, retType
    global depFunExpr, listAllFunExpr
    checker = translator.ReadQuery(bmExpr)
    for expr in bmExpr:
        if expr[0] == 'synth-fun': # 合成函数表达式
            synFunExpr = expr
            synFunName = expr[1] # 函数名
            for i, e in enumerate(expr[2]):
                synFunName2Num[e[0]] = i

    retType = {startSym: synFunExpr[3]} # 将起始符号对应的返回类型设置为合成函数表达式

    for term in synFunExpr[4]: # 遍历合成函数表达式中的每个项
        tName = term[0] # 获取项中的第一个元素作为项名
        prodRules[tName] = [] # 创建一个空列表作为规则列表

    for term in synFunExpr[4]:
        tName = term[0]
        tType = term[1]

        if tType == retType[startSym]:
            prodRules[startSym].append(parseRule(tName))

        retType[tName] = tType
        for expr in term[2]:
            prodRules[tName].append(parseRule(expr))
        depFunExpr[tName] = [[] for i in range(100)]

    if len(synFunExpr[4]) == 1:
        prodRules.pop(startSym)
        startSym = synFunExpr[4][0][0]

    for dep in range(1, 40):
        for term in prodRules.keys():
            genDepExpr(term, dep)
        for funExpr in depFunExpr[startSym][dep]:
            strExpr = outpExpr(funExpr.expr)
            if checker.check(strExpr) is None:
                print(strExpr)
                with open('result.txt', 'w') as f:
                    f.write(strExpr)
                    return
