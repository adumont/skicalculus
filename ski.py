def reverse_copy(x: lst) -> lst:
    return [x[i] for i in range(len(x)-1, -1, -1)]

def exprToStr(expr:list) -> str:
    """ Takes a SKI expression in a list form and returns a formated string
    """
    out = ""
    for e in expr:
        if type(e) == type(""):
            out = f"{out}{e}"
        elif type(e) == type([]):
            out= f"{out}({ exprToStr(e) })"
        else:
            raise Exception(f"Expected list or str, {e} is {type(e)}")
    return out


def abstract(expr: list, var:str) -> list:
    """ Abstract expr with respect to var

        Args:
            expr: list representing the expected result
            var: str representing the variable

        Returns:
            list representing the combinator, not depending on var

        Examples: \y.yx
            abstract(["y", "x"], "y") = ['S', 'I', ['K', 'x']]
    """

    def dependson(expr:list|str, var:str) -> bool:
        """ Returns True if expr depends on var

            Args:
                expr: list representing the expected result
                var: str representing the variable

            Returns:
                bool: True if expr depends on var

            Examples:
                dependson(["K", "I"], "x") = False
                dependson(["K", ["x", "S"]], "x") = True
        """
        if expr == []:
            return False
        elif type(expr) == str:
            return expr==var
        else:
            return dependson(expr[0], var) or dependson(expr[1:], var)


    if len(expr) == 1:
        if expr[0] == var:
            return "I"
        else:
            return ["K", expr[0]]
    elif not dependson(expr,var):
        return ["K", expr]
    else:
        return ["S", abstract(expr[0:-1], var), abstract(expr[-1], var) ]


def SKI_solve(expr:list, vars:str|list):
    """ Express the expr as a combinator applied to var(s)
    """

    if type(vars) == str:
        vars = [vars]

    vars = [ v for v in vars ] # copy
    vars.reverse() # in place

    for v in vars:
        expr = abstract(expr, v)

    return expr


def clean(expr:list) -> list:
    if expr == []:
        return []

    if type(expr[0]) == list:
        res = clean(expr[0])
    else:
        res = [ expr[0] ]

    if len(expr)>1:
        for e in expr[1:]:
            if type(e) == str:
                res.append(e)
            elif len(e) == 1:
                while type(e) == list and len(e) == 1:
                    e = e[0]
                res.append(e)
            else:
                res.append(clean(e))
    return res


def reduce(expr:list) -> list:
    def _reduce(expr:list) -> list:
        while type(expr[0]) == list:
            expr=clean(expr)

        if expr == []: return []
        elif expr[0] == "S" and len(expr)>=4:
            x,y,z = expr[1:4]
            return [ x, z, [y, z] ] + expr[4:]
        elif expr[0] == "K" and len(expr)>=3:
            x,y = expr[1:3]
            return [ x ] + expr[3:]
        elif expr[0] == "I" and len(expr)>=2:
            x = expr[1]
            return [ x ] + expr[2:]
        else:
            res = []
            for e in expr:
                if type(e)==str:
                    res.append(e)
                else:
                    res = res + [ clean(reduce(e)) ]
            return res

    return clean(_reduce(expr))


def repeat_reduce(expr:list) -> list:
    while True:
        new = reduce(expr)
        if new == expr: break
        expr = new
    return expr


pairs= [
    [ ["S", ["K","K"],"I"] , ["K"]      ],
    [ ["S", "K"]           , ["K", "I"] ],
]

def simplify(expr:list) -> list:
    """ Substitute known SKI identities to smplify the expression
    """
    for b,c in pairs:
        if len(expr)>=len(b):
            if expr[0:len(b)] == b: # we apply simplification on the head of the list only
                expr=c+expr[len(b):]

    # print(expr)

    res = []
    for e in expr:
        if type(e) == str:
            res.append(e)
        else:
            res.append(simplify(e))

    return clean(res)


def parse(expr:str) -> list:
    def _parse(expr:str) -> (str, list):
        l = []
        while len(expr)>0:
            c=expr[0]
            expr=expr[1:]
            if c<=" ": continue
            if c=="(":
                s,expr = _parse(expr)
                l.append(s)
                continue
            if c == ")":
                break
            l.append(c)
        return l, expr

    return clean(_parse(expr)[0])


def from_lambda(expr:str) -> [str,str]:
    """ returns an SKI expression and variables from a string of a lambda abstraction
    """
    vars, body = list(map(parse, expr.replace("\\","").split(".")))
    return SKI_solve(vars=vars, expr=body), vars


def forth_ski(expr:list) -> str:
    """ Converts a SKI expresion (as list) to a FORTH SKI sentence as str
    """
    def _forth_ski(expr:list) -> list:
        """ Converts a SKI expresion (as list) to a FORTH SKI sentence as list
        """
        expr=[e for e in expr] # copy
        expr.reverse()
        out=[]
        for c in expr:
            if type(c) == str:
                out.append(c)
            else:
                out+=_forth_ski(c)
        out.append( ")"*(len(expr)-1) )
        return out

    return " ".join( _forth_ski(expr) )

def main():
    return

if __name__ == "main":
    main()