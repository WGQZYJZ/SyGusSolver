import sys
import sexp
import pprint
import translator
import numpy as np
import multiprocessing
import random
import time

np.seterr(all="ignore")
mask = (1 << 64) - 1
bvFun = {
    'bvnot': lambda x: x ^ mask, # python的整数为补码编码，不能直接取反
    'bvand': lambda x, y: x & y,
    'bvor': lambda x, y: x | y,
    'bvxor': lambda x, y: x ^ y,
    'bvadd': lambda x, y: x + y,
    'bvlshr': lambda x, y: x >> y,
    'bvshl': lambda x, y: x << y,
    'not': lambda x: not x,
    'and': lambda x, y: x and y,
    'or': lambda x, y: x or y,
    '+': lambda x, y: x + y,
    '-': lambda x, y: x - y,
    '*': lambda x, y: x * y,
    'mod': lambda x, y: x % y,
    '<=': lambda x, y: x <= y,
    '>=': lambda x, y: x >= y,
    '=': lambda x, y: x == y,
    'ite': lambda x, y, z: (x != 0) * y + (x == 0) * z,
}
allFun = bvFun.copy()
tot = 0
cons = []
allFInp = []
allFOutp = []
synFunExpr = []
synFunName = ''
synFunName2Num = {}
startSym = 'My-Start-Symbol'
prodRules = {startSym: []}
retType = {}
hashMul = []
setFunExpr = {startSym: set()}
depFunExpr = {startSym: [[] for i in range(100)]}
listAllFunExpr = []
exprCons = []


def stripComments(bmFile):
    noComments = "(\n"
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + "\n)"


# 表示合成函数表达式
class FunExpr:
    def __init__(self, term, expr, leng, f, ret):
        super().__init__()
        self.term = term
        self.expr = expr
        self.leng = leng
        self.f = f
        self.ret = np.array(ret, dtype='uint64')
        self.hs = int((self.ret * hashMul).sum())

    def __hash__(self):
        return self.hs

    def __eq__(self, other):
        if type(other) == FunExpr:
            if self.hs != other.hs:
                return False
            return np.all(self.ret == other.ret)
        return False


# 构建合成问题的解空间树
class treeNode:
    def __init__(self, ls, rs, classFun, evalFun, consL):
        super().__init__()
        self.ls = ls
        self.rs = rs
        self.classFun = classFun
        self.evalFun = evalFun
        self.consL = consL

    def reinit(self, ls, rs, classFun, evalFun, consL):
        self.ls = ls
        self.rs = rs
        self.classFun = classFun
        self.evalFun = evalFun
        self.consL = consL

    def isLeaf(self):
        return self.ls == None and self.rs == None

    def getNext(self, x):
        return self.ls if listAllFunExpr[self.classFun].f(x) == 1 else self.rs


# 解析函数含义
def parseDefFun(expr):
    assert expr[0] == 'define-fun'
    name = expr[1]
    inFormat = expr[2]
    fun = expr[4]
    name2Num = {}

    for i, v in enumerate(inFormat):
        name2Num[v[0]] = i

    def f(expr):
        if type(expr) == list:
            ret = [f(e) for e in expr[1:]]
            oprF = allFun[expr[0]]
            return lambda *a: oprF(*[f(*a) for f in ret])
        elif type(expr) == tuple:
            return lambda *a: np.uint64(expr[1])
        else:
            return lambda *a, i=name2Num[expr]: a[i]

    allFun[name] = f(expr[4])


# 添加约束
def assertCons(expr):
    assert expr[0] == '='
    if type(expr[1]) is tuple:
        tmp = expr[1]
        expr[1] = expr[2]
        expr[2] = tmp
    assert type(expr[1]) is list
    assert expr[1][0] == synFunName

    for e in expr[1][1:]:
        assert type(e) is tuple
        assert tuple(e[0]) == ('BitVec', ('Int', 64))
    assert type(expr[2]) is tuple
    assert tuple(expr[2][0]) == ('BitVec', ('Int', 64))


# 解析约束表达式
def parseCons(expr):
    allFInp.append([e[1] for e in expr[1][1:]])
    allFOutp.append(expr[2][1])


# 解析语法规则
def parseRule(expr):
    idx, idy = 0, 0
    listT = []

    def f(e):
        if type(e) == list:
            ret = [f(w) for w in e[1:]]
            oprF = allFun[e[0]]
            return lambda *a: lambda *b: oprF(*[ff(*a)(*b) for ff in ret])
        elif type(e) == tuple:
            return lambda *a: lambda *b: np.uint64(e[1])
        elif e in prodRules:
            nonlocal idx
            idx += 1
            return lambda *a, i=idx - 1: a[i]
        else:
            return lambda *a, i=synFunName2Num[e]: lambda *b: b[i]

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

    s = (expr, listT, f(expr), g(expr))
    return s


# 生成合成函数中非终结符的可能表达式
def genDepExpr(term, dep):
    for expr, listT, funF, exprF in prodRules[term]:
        numT = len(listT)
        listFE = [None] * numT

        def dfsExpr(idx, leng):
            global tot
            tot += 1
            if idx == numT:
                if leng != dep:
                    return
                if type(expr) == list and numT == 2 and len(expr) == 3:
                    if (
                        expr[0] == 'bvand'
                        or expr[0] == 'bvor'
                        or expr[0] == 'bvxor'
                        or expr[0] == 'bvadd'
                    ) and listFE[0].__hash__() > listFE[1].__hash__():
                        return

                newExpr = exprF(*[w.expr for w in listFE])
                fl = [w.f for w in listFE]
                newF = lambda *a, tf=funF: tf(*fl)(*a)
                if type(expr) == list and numT + 1 == len(expr) and expr[0] in allFun:
                    newRet = allFun[expr[0]](*[funExpr.ret for funExpr in listFE])
                else:
                    newRet = newF(*allFInp)
                funExpr = FunExpr(term, newExpr, dep, newF, newRet)
                if funExpr not in setFunExpr[term]:
                    setFunExpr[term].add(funExpr)
                    depFunExpr[term][dep].append(funExpr)
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


# 将合成函数的表达式转换为字符串形式
def outpExpr(expr):
    global synFunExpr
    fullExpr = ['define-fun'] + synFunExpr[1:4] + [expr]
    strExpr = translator.toString(fullExpr, ForceBracket=True)
    return strExpr


# 检索解空间
def search(node, x):
    if node.isLeaf():
        return node
    return search(node.getNext(x), x)


# 从树节点中获取合成函数的表达式
def getTreeExpr(node):
    if node.isLeaf():
        return listAllFunExpr[node.evalFun].expr
    else:
        lExpr = getTreeExpr(node.ls)
        rExpr = getTreeExpr(node.rs)
        return ['if0', listAllFunExpr[node.classFun].expr, lExpr, rExpr]


def solve(bmExpr, ansQueue, flag):
    global tot, cons, allFInp, allFOutp, synFunExpr, synFunName, synFunName2Num
    global startSym, prodRules, retType, hashMul, setFunExpr
    global depFunExpr, listAllFunExpr, exprCons, mask
    checker = translator.ReadQuery(bmExpr)

    # 提取语法、定义和约束
    for expr in bmExpr:
        assert expr[0] != 'declare-var'
        if expr[0] == 'synth-fun':
            synFunExpr = expr
            synFunName = expr[1]
            mask = (1 << expr[3][2][1]) - 1 # 确定掩码值
            for i, e in enumerate(expr[2]):
                synFunName2Num[e[0]] = i
        elif expr[0] == 'define-fun':
            parseDefFun(expr)
        elif expr[0] == 'constraint':
            assertCons(expr[1])
            parseCons(expr[1])
            cons.append(expr[1])

    remCons = len(allFInp)
    exprCons = [[] for i in range(remCons)]
    allFInp = [np.array(t, dtype = 'uint64') for t in zip(*allFInp)]
    allFOutp = np.array(allFOutp, dtype = 'uint64')
    retType = {startSym: synFunExpr[3]}
    hashMul = np.array(
        [pow(19491001, i, 1 << 64) for i in range(len(allFInp))], dtype='uint64'
    )

    for term in synFunExpr[4]:
        tName = term[0]
        prodRules[tName] = []

    hasIf0 = False

    for term in synFunExpr[4]:
        tName = term[0]
        tType = term[1]

        if tType == retType[startSym]:
            prodRules[startSym].append(parseRule(tName))

        retType[tName] = tType
        for expr in term[2]:
            prodRules[tName].append(parseRule(expr))
            if type(expr) == list and expr[0] == 'if0':
                hasIf0 = True
                continue
        setFunExpr[tName] = set()
        depFunExpr[tName] = [[] for i in range(100)]

    if len(synFunExpr[4]) == 1:
        prodRules.pop(startSym)
        startSym = synFunExpr[4][0][0]

    if not hasIf0:
        for dep in range(1, 20):
            for term in prodRules.keys():
                genDepExpr(term, dep)
            for funExpr in depFunExpr[startSym][dep]:
                if np.all(funExpr.ret == allFOutp):
                    strExpr = outpExpr(funExpr.expr)
                    assert checker.check(strExpr) is None
                    print(strExpr)
                    ansQueue.put(strExpr)
                    return

    # 循环尝试不同深度的生成，直到找到符合约束条件的合成函数表达式
    genDep = 0
    for dep in range(1, 20):
        # 遍历合成函数中的每个非终结符
        for term in prodRules.keys():
            genDepExpr(term, dep)
        genDep = dep
        # 遍历生成的深度为dep的合成函数表达式
        for funExpr in depFunExpr[startSym][dep]:
            idxFE = len(listAllFunExpr)
            listAllFunExpr.append(funExpr)
            outp = funExpr.ret == allFOutp
            pos = list(np.where(outp)[0])
            for p in pos:
                if len(exprCons[p]) == 0:
                    remCons -= 1
                exprCons[p].append(idxFE)
        if remCons == 0:
            break

    lsCons = [(i, len(ls)) for i, ls in enumerate(exprCons)]
    if flag:
        lsCons = sorted(lsCons, key=lambda x: x[1])
    else:
        random.shuffle(lsCons)
    treeRoot = treeNode(None, None, None, None, [])
    for i, _ in lsCons:
        inp, outp = [t[i] for t in allFInp], allFOutp[i]
        node = search(treeRoot, inp)
        if node.evalFun is None:
            for w in exprCons[i]:
                node.evalFun = w
                break
        if node.evalFun in exprCons[i]:
            node.consL.append(i)
            continue
        arrInp = [t[node.consL] for t in allFInp]
        evalI = None
        for w in exprCons[i]:
            evalI = w
            break

        founded = False
        for idFE, funExpr in enumerate(listAllFunExpr):
            arr1 = funExpr.f(*arrInp) == 1
            i1 = funExpr.f(*inp) == 1
            if np.all(arr1) and not i1:
                lsNode = treeNode(None, None, None, node.evalFun, node.consL)
                rsNode = treeNode(None, None, None, evalI, [i])
                node.reinit(lsNode, rsNode, idFE, None, [])
                founded = True
                break
            elif not np.any(arr1) and i1:
                lsNode = treeNode(None, None, None, evalI, [i])
                rsNode = treeNode(None, None, None, node.evalFun, node.consL)
                node.reinit(lsNode, rsNode, idFE, None, [])
                founded = True
                break

        # 如果还没有找到符合条件的合成函数，继续循环生成
        while not founded:
            genDep += 1
            for term in prodRules.keys():
                genDepExpr(term, genDep)
            startId = len(listAllFunExpr)
            for funExpr in depFunExpr[startSym][genDep]:
                listAllFunExpr.append(funExpr)
            for tid, funExpr in enumerate(listAllFunExpr[startId:]):
                idFE = tid + startId
                arr1 = funExpr.f(*arrInp) == 1
                i1 = funExpr.f(*inp) == 1
                if np.all(arr1) and not i1:
                    lsNode = treeNode(None, None, None, node.evalFun, node.consL)
                    rsNode = treeNode(None, None, None, evalI, [i])
                    node.reinit(lsNode, rsNode, idFE, None, [])
                    founded = True
                    break
                elif not np.any(arr1) and i1:
                    lsNode = treeNode(None, None, None, evalI, [i])
                    rsNode = treeNode(None, None, None, node.evalFun, node.consL)
                    node.reinit(lsNode, rsNode, idFE, None, [])
                    founded = True
                    break

    expr = getTreeExpr(treeRoot)
    strExpr = outpExpr(expr)
    assert (checker.check(strExpr)) is None
    ansQueue.put(strExpr)


# 实现每次进程数为processCnt，时限为timeLimit的并发，以尝试解决不完备性
# 以原默认解答为初始值，后用循环并发进行随机采样，如果出现长度更短者（正确性不保证，直觉使然），则认为是更优解，替换
def bvsolver(bmExpr, processCnt, timeLimit):
    ansQueue = multiprocessing.Queue()

    process = multiprocessing.Process(target=solve, args = (bmExpr, ansQueue, True))
    process.start()
    process.join()
    ans = ansQueue.get()
    processList = [i for i in range(processCnt)]

    time_start = time.perf_counter()
    while(time.perf_counter() - time_start < timeLimit):
        for i in range(processCnt):
            processList[i] = multiprocessing.Process(target = solve, args = (bmExpr, ansQueue, False))

        for i in range(processCnt):
            processList[i].start()

        for i in range(processCnt):
            processList[i].join()

        while not ansQueue.empty():
            ansTmp = ansQueue.get()
            if(len(ansTmp) < len(ans)):
                ans = ansTmp

    return ans
