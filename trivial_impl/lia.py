from copy import deepcopy
import functools
import translator

def getArgsStr(expr):
    if isinstance(expr, tuple) and expr[1].isdigit():
        return [str(expr[1])]
    if isinstance(expr, str):
        return [expr]
    ret = []
    if isinstance(expr, list):
        for val in expr:
            ret += getArgsStr(val)
    return ret

# 将一个列表或元组中的每个元素递归地转换为元组，并返回一个新的元组。
# 如果列表或元组中的某个元素是字符串并且在arglist中，则返回"arg"加上该元素在arglist中的索引。
# 否则，返回原始列表或元组中的元素。
def listToTuple(List, arglist):
    if isinstance(List, list) or isinstance(List, tuple):
        return tuple(listToTuple(i, arglist) for i in List)
    assert(isinstance(List, str))
    if List in arglist:
        return "arg" + str(arglist.index(List))
    return List

def getCandidates(bmExpr):
    ret = []

    #递归地从一个表达式中提取参数列表
    def get(expr, funcname):
        res = []
        if not(isinstance(expr, list) or isinstance(expr, tuple)):
            return []
        if len(expr) == 1:
            return get(expr[0], funcname)
        if expr[0] in ["=", ">=", "<="]:
            expr1, expr2 = expr[1], expr[2]
            if not isinstance(expr1, list):
                expr1, expr2 = expr2, expr1
            if not isinstance(expr1, list):
                return []
            if type(expr2) not in [str, tuple, list]:
                return []
            if isinstance(expr2, tuple) and isinstance(expr2[1], int):
                return [expr2[1]]
            if not isinstance(expr1, list):
                arglist = []
            if expr1[0] == funcname:
                arglist = expr1[1:]
            args = arglist + ["+", "-", "*"]
            if expr2 in args:
                return ["arg" + str(args.index(expr2))]
            values = getArgsStr(expr2)
            ins = [val in args for val in values]
            isAvail = functools.reduce(lambda x, y: x and y, ins, True)
            if isAvail:
                return [listToTuple(expr2, arglist)]
            return []

        for exprs in expr:
            res += get(exprs, funcname)
        return res
    
    funcname = None
    for expr in bmExpr:
        if not isinstance(expr, list):
            continue
        if len(expr) < 1:
            continue
        if expr[0] == "synth-fun":
            funcname = expr[1]
        if expr[0] == "constraint":
            curCandidates = get(expr[1:], funcname)
            ret += curCandidates
    return ret

def generateTestcase(varlist):
    length = len(varlist)
    ret = []
    temp = [0] * length
    for i in range(length):
        for j in range(length):
            if j == i:
                continue
            temp[i] = 2
            temp[j] = 1
            dic = {varlist[t] : temp[t] for t in range(length)}
            ret.append(dic)
            temp[i] = 2
            temp[j] = 2
            dic = {varlist[t] : temp[t] for t in range(length)}
            ret.append(dic)
            temp[i] = temp[j] = 0
    for i in range(length):
        temp[i] = 2
        dic = {varlist[t] : temp[t] for t in range(length)}
        ret.append(dic)
        temp[i] = 0
    return ret

def constraintEval(info_dic, constraint, testcase, funcdic):
    if isinstance(constraint, tuple) and isinstance(constraint[1], int):
        return constraint[1]
    if isinstance(constraint, list) or isinstance(constraint, tuple):
        if constraint[0] in ["and", "or"]:
            val1 = constraintEval(info_dic, constraint[1], testcase, funcdic)
            if constraint[0] == "and" and not val1:
                return False
            if constraint[0] == "or" and val1:
                return True
            val2 = constraintEval(info_dic, constraint[2], testcase, funcdic)
            if constraint[0] == "and":
                return val1 and val2
            else:
                return val1 or val2
        if constraint[0] == "=>":
            val1 = constraintEval(info_dic, constraint[1], testcase, funcdic)
            if not val1:
                return True
            val2 = constraintEval(info_dic, constraint[2], testcase, funcdic)
            return val2
        if constraint[0] in ["=", "<=", "<", ">", ">=", "+", "-", "*"]:
            val1 = constraintEval(info_dic, constraint[1], testcase, funcdic)
            val2 = constraintEval(info_dic, constraint[2], testcase, funcdic)
            op = constraint[0]
            if op == "=":
                op = "=="
            return eval(str(val1) + op + str(val2))
        funcname = info_dic["funcname"]
        if constraint[0] == funcname:
            candval = funcdic[tuple(constraint[1:])]
            if isinstance(candval, int):
                return candval
            elif isinstance(candval, tuple):
                argdic = dict()
                for i, arg in enumerate(constraint[1:]):
                    argdic["arg" + str(i)] = arg
                info_dic["argdic"] = argdic
                return constraintEval(info_dic, list(candval), testcase, funcdic)
            else:
                arg = int(candval[3:])
                assert(constraint[arg + 1] in testcase)
                return testcase[constraint[arg + 1]]
    assert(isinstance(constraint, str))
    if constraint not in testcase:
        constraint = info_dic["argdic"][constraint]
    return testcase[constraint]

def checkoneAssign(info_dic, constraints, testcase, funcdic):
    for constraint in constraints:
        if not constraintEval(info_dic, constraint[1], testcase, funcdic):
            return False
    return True

def filterFunc(info_dic):
    def get(constraint, funcname):
        retlist = []
        if isinstance(constraint, list):
            if constraint[0] == funcname:
                return [tuple(constraint[1:])]
            for child in constraint:
                retlist += get(child, funcname)
        return retlist
    ret = []
    funcName = info_dic["funcname"]
    constraints = info_dic["constraint"]
    for constraint in constraints:
        ret += get(constraint, funcName)
    return list(set(ret))

# 根据给定的输入信息字典，通过深度优先搜索算法生成一个满足约束条件的赋值列表
def partiTest(info_dic):
    constraints = info_dic["constraint"]
    candidates = info_dic["candidate"]
    testcases = info_dic["test"]
    fullset = set()
    funccalls = filterFunc(info_dic)
    for testcase in testcases:   
        funclist = []
        for funccall in funccalls:
            assign = tuple(funccall)
            funclist.append(assign)
        tryretvalue = []
        assigndic = {}
        def dfs(funclist, assigndic, tryretvalue, depth, maxdepth):
            if depth == maxdepth:
                tryretvalue.append(deepcopy(assigndic))
                return
            for candidate in candidates:
                assigndic[funclist[depth]] = candidate
                dfs(funclist, assigndic, tryretvalue, depth + 1, maxdepth)
            return
        dfs(funclist, assigndic, tryretvalue, 0, len(funclist))
        for assign in tryretvalue:
            if checkoneAssign(info_dic, constraints, testcase, assign):
                break
        for item in assign.items():
            item = (tuple(testcase[x] for x in item[0]), item[1])
            fullset.add(item)
    full_list = [[] for _ in range(len(candidates))]
    for pair in fullset:
        full_list[candidates.index(pair[1])].append(pair[0])
    return full_list

# 过滤测试集
def filterTestset(condition_list, testset):
    retset = set()
    for test in testset:
        sat = True
        for cond in condition_list:
            op = cond[0]
            if op == "=":
                op = "=="
            sat = eval(str(test[cond[1]]) + op + str(test[cond[2]]))
            if not sat:
                break
        if sat:
            retset.add(test)
    return retset

def search(info_dic, depth, full_list):
    if depth == info_dic["maxdepth"]:
        return
    cur_set = set(full_list[depth])
    append_set = set([item for sublist in full_list[depth + 1:] for item in sublist])
    oplist = ["<=", "=", "<"]
    arglen = info_dic["arglen"]
    condition_list = info_dic["condition"][depth]
    if len(append_set) == 0:
        return
    for i in range(arglen):
        for j in range(arglen):
            if i == j:
                continue
            for op in oplist:
                condition_list.append([op, i, j])
                new_cur_set = filterTestset(condition_list, cur_set)
                new_append_set = filterTestset(condition_list, append_set)
                curlen = len(cur_set)
                apdlen = len(append_set)
                new_curlen = len(new_cur_set)
                new_apdlen = len(new_append_set)
                if curlen != new_curlen or apdlen == new_apdlen:
                    condition_list.pop(-1)
                elif new_apdlen == 0:
                    search(info_dic, depth + 1, full_list)
                    return
                else:
                    append_set = new_append_set
    assert(False)   # should not execute here
    return

def candiToarg(candidate, args):
    if isinstance(candidate, tuple) or isinstance(candidate, list):
        return [candiToarg(v, args) for v in candidate]
    if isinstance(candidate, int):
        return str(candidate)
    if candidate[:3] == "arg":
        return args[int(candidate[3:])]
    return candidate

def buildCondition(conditions, args):
    if len(conditions) == 1:
        if conditions[0][0] != "<":
            return [conditions[0][0], args[conditions[0][1]], args[conditions[0][2]]]
        else:
            return ["not"] + [[">=", args[conditions[0][1]], args[conditions[0][2]]]]
    ret = ["and"] + [buildCondition(conditions[0:1], args)] + [buildCondition(conditions[1:], args)]
    return ret

def solve(bmExpr):
    candidates = getCandidates(bmExpr)

    candidates = list(set(candidates))
    dic = {}
    for i, candi in enumerate(candidates):
        dic[candi] = i
    
    constraints = []
    for expr in bmExpr:
        if not isinstance(expr, list):
            continue
        if len(expr) < 1 or expr[0] != "constraint":
            continue
        constraints.append(expr)
    
    varlist = []
    for expr in bmExpr:
        if isinstance(expr, list) and expr[0] == "declare-var":
            varlist.append(expr[1])
    
    maxdepth = len(candidates) - 1
    conditions = [[] for _ in range(maxdepth)]
    depth = 0

    synth = None
    for expr in bmExpr:
        if expr[0] == "synth-fun":
            synth = expr
            break
    
    funcname = synth[1]
    testcases = generateTestcase(varlist)
    info_dic = {}
    info_dic["candidate"] = candidates
    info_dic["condition"] = conditions
    info_dic["maxdepth"] = maxdepth
    info_dic["constraint"] = constraints
    info_dic["test"] = testcases
    info_dic["arglen"] = len(synth[2])
    info_dic["funcname"] = funcname
    info_dic["synth"] = synth
    full_list = partiTest(info_dic)
    search(info_dic, depth, full_list)
    funcDefine = ["define-fun"] + info_dic["synth"][1:4]
    funcDefineStr = translator.toString(funcDefine, ForceBracket=True)
    args = tuple(v[0] for v in info_dic["synth"][2])
    assert(len(candidates) - 1 == len(conditions))
    def dfs(candidates, args, conditions, depth):
        if depth == len(candidates) - 1:
            return candiToarg(candidates[-1], args)
        curconditions = conditions[depth]
        assert(len(curconditions) > 0)
        conditionStr = buildCondition(curconditions, args)
        return ["ite"] + [conditionStr] + [candiToarg(candidates[depth], args)] + [dfs(candidates, args, conditions, depth + 1)]
    curStr = dfs(candidates, args, conditions, depth=0)
    curStr = translator.toString(curStr)
    ans = funcDefineStr[:-1] + " " + curStr + funcDefineStr[-1]
    return ans