import sys

import lark
import z3


class CompileError(BaseException):

  def __init__(self, msg):
    self.msg = msg


def get_line(node):
  try:
    if node.line is not None:
      return node.line
  except:
    pass
  return get_line(node.children[0])

def get_column(node):
  try:
    if node.column is not None:
      return node.column
  except:
    pass
  return get_column(node.children[0])

def error(err, node):
  line = get_line(node)
  column = get_column(node)
  e = ''
  e += 'Error at %d:%d:\n' % (line, column)
  e += '  ' + source.split('\n')[line - 1] + '\n'
  e += '  ' + ' '*(column - 1) + '^\n'
  e += err + '\n'
  raise CompileError(e)


class Function:

  def __init__(self, decl):
    self.name = decl['name'][0]
    self.params = decl['params'].children
    self.ret = decl['ret'][0]

    self.require = [r['cond'][0] for r in decl['reqs'].children if r.data == 'require']
    self.ensure = [r['cond'][0] for r in decl['reqs'].children if r.data == 'ensure']

    self.body = decl['body']


class LocalContext:

  def __init__(self):
    self.vals = []
    self.vars = {}
    self.knowledge = []

  def push(self):
    # TODO: Could make this more efficient by referencing parent
    cxt = LocalContext()
    cxt.vals = list(self.vals)
    cxt.vars = dict(self.vars)
    cxt.knowledge = list(self.knowledge)
    return cxt

  def val_name(self, name_hint):
    name = name_hint.upper()
    suffix = 0
    while name in self.vals:
      suffix += 1
      name = name_hint.upper() + str(suffix)
    return name

  def new_val(self, name_hint):
    name = self.val_name(name_hint)
    self.vals.append(name)
    return z3.Int(name)

  def assume(self, formula):
    if type(formula) is list:
      self.knowledge += formula
    else:
      self.knowledge.append(formula)

  def prove(self, formula, error_node):
    solver = z3.Solver()
    for hyp in self.knowledge:
      solver.add(hyp)
    solver.add(z3.Not(formula))

    result = solver.check()
    if result != z3.unsat:
      err = ''
      err += 'Failed to prove: ' + str(formula) + '\n'
      err += 'in context:\n' + str(self)
      if result == z3.sat:
        err += 'Counterexample: ' + str(solver.model()) + '\n'
      else:
        err += 'Z3 failed\n'
      err = err[:-1]
      error(err, error_node)

  def __repr__(self):
    s = ''
    for x, v in self.vars.items():
      s += '  ' + x + ' -> ' + str(v) + '\n'
    for k in self.knowledge:
      s += '  ' + str(k) + '\n'
    return s


def interpret_iexpr(expr, cxt, global_context, subst={}):
  if expr.data == 'ilit':
    return z3.IntVal(int(str(expr[0])))

  elif expr.data == 'ivar':
    x = expr[0].value
    if x in subst:
      return subst[x]
    if x not in cxt.vars:
      error('Undeclared variable', expr)
    return cxt.vars[x]

  elif expr.data == 'iunop':
    i1 = interpret_iexpr(expr[1], cxt, global_context, subst)
    return {
      '+': i1,
      '-': -i1,
    }[str(expr[0])]

  elif expr.data == 'ibinop':
    i1 = interpret_iexpr(expr[0], cxt, global_context, subst)
    i2 = interpret_iexpr(expr[2], cxt, global_context, subst)
    return {
      '+': i1 + i2,
      '-': i1 - i2,
    }[str(expr[1])]

  elif expr.data == 'icall':
    func = expr[0].value
    if func not in global_context:
      error('Undeclared function', expr)
    func = global_context[func]

    args = [interpret_iexpr(arg, cxt, global_context, subst) for arg in expr.children[1:]]
    if len(func.params) != len(args):
      error('Wrong number of arguments', expr)
    psubst = {func.params[i].value: args[i] for i in range(len(func.params))}

    for pre in func.require:
      cxt.prove(interpret_bexpr(pre, cxt, global_context, psubst), expr)

    psubst[func.ret.value] = cxt.new_val(func.name)
    for post in func.ensure:
      cxt.assume(interpret_bexpr(post, cxt, global_context, psubst))
    return psubst[func.ret.value]

  raise NotImplementedError(expr)


def interpret_bexpr(expr, cxt, global_context, subst={}):
  if expr.data == 'blit':
    return z3.BoolVal({
        'true': True,
        'false': False,
      }[str(expr[0])])

  elif expr.data == 'bunop':
    if str(expr[0]) == '~':
      return z3.Not(interpret_bexpr(expr[1], cxt, global_context, subst))

  elif expr.data == 'bbinop':
    b1 = interpret_bexpr(expr[0], cxt, global_context, subst)
    b2 = interpret_bexpr(expr[2], cxt, global_context, subst)
    return {
      '/\\': z3.And(b1, b2),
      '\\/': z3.Or(b1, b2),
      '->': z3.Implies(b1, b2),
      '<->': b1 == b2,
    }[str(expr[1])]

  elif expr.data == 'bicomp':
    exprs = []
    for i in range(0, len(expr.children) - 1, 2):
      i1 = interpret_iexpr(expr[i], cxt, global_context, subst)
      i2 = interpret_iexpr(expr[i + 2], cxt, global_context, subst)
      exprs.append({
          '=': i1 == i2,
          '<>': i1 != i2,
          '<=': i1 <= i2,
          '<': i1 < i2,
          '>=': i1 >= i2,
          '>': i1 > i2,
        }[str(expr[i + 1])])
    return exprs[0] if len(exprs) == 1 else z3.And(exprs)

  raise NotImplementedError(expr)


def interpret_block(stmts, cxt, global_context, posts):
  for i in range(len(stmts)):
    stmt = stmts[i]

    if stmt.data == 'ensure':
      cxt.prove(interpret_bexpr(stmt['cond'][0], cxt, global_context), stmt)

    elif stmt.data == 'assert':
      cxt.assume(interpret_bexpr(stmt['cond'][0], cxt, global_context))

    elif stmt.data == 'assign':
      x = stmt['var'][0].value
      if x not in cxt.vars:
        error('Undeclared variable', stmt['var'])
      cxt.vars[x] = interpret_iexpr(stmt['value'][0], cxt, global_context)

    elif stmt.data == 'decl':
      for var in stmt:
        x = var.value
        if x in cxt.vars:
          error('Variable name already used', var)
        cxt.vars[x] = cxt.new_val('?' + x)

    elif stmt.data == 'discard':
      interpret_iexpr(stmt['value'][0], cxt, global_context)

    elif stmt.data == 'return':
      break

    elif stmt.data == 'if':
      # Alternate approach:
      # For each variable x assigned in bodies, create a new value X representing
      # the value after the branch
      # For each body, interpret with pushed condition assumptions C
      # Check value x -> E and replace with x -> X and knowledge X = E
      # Move knowledge back to original context, prefaced with C ->
      # After all branches are done, learn x -> X

      prevconds = []

      cxt0 = cxt.push()
      cxt0.assume(interpret_bexpr(stmt['cond'][0], cxt0, global_context))
      interpret_block(stmt['body'].children + stmts[i+1:], cxt0, global_context, posts)
      prevconds.append(stmt['cond'][0])

      for branch in stmt['elifs']:
        cxt0 = cxt.push()
        for cond in prevconds:
          cxt0.assume(z3.Not(interpret_bexpr(cond, cxt0, global_context)))
        cxt0.assume(interpret_bexpr(branch['cond'][0], cxt0, global_context))
        interpret_block(branch['body'].children + stmts[i+1:], cxt0, global_context, posts)
        prevconds.append(branch['cond'][0])

      elsebody = [] if len(stmt['else'].children) == 0 else stmt['else'][0].children
      cxt0 = cxt.push()
      for cond in prevconds:
        cxt0.assume(z3.Not(interpret_bexpr(cond, cxt0, global_context)))
      interpret_block(elsebody + stmts[i+1:], cxt0, global_context, posts)

      return

    else:
      raise NotImplementedError(stmt)

  for post in posts:
    cxt.prove(interpret_bexpr(post, cxt, global_context), post)


def check_function(func, global_context):
  cxt = LocalContext()

  for param in func.params:
    x = param.value
    if x in cxt.vars:
      error('Variable name already used', param)
    cxt.vars[x] = cxt.new_val(x)

  for pre in func.require:
    cxt.assume(interpret_bexpr(pre, cxt, global_context))

  r = func.ret.value
  if r in cxt.vars:
    error('Variable name already used', func.ret)
  cxt.vars[r] = cxt.new_val('?' + r)
  # cxt.vars[r] = z3.IntVal(0)

  interpret_block(func.body.children, cxt, global_context, func.ensure)


def tree_get_child(self, key):
  if type(key) is str:
    for c in self.children:
      if type(c) is lark.Tree and c.data == key:
        return c
  if type(key) is int:
    return self.children[key]
  print(self.pretty())
  raise KeyError(str(key))
lark.Tree.__getitem__ = tree_get_child

with open('grammar.lark', 'r') as f:
  parser = lark.Lark(f.read())


def compile(src):
  global source
  source = src

  ast = parser.parse(source)

  global_context = {}
  for decl in ast.children:
    func = Function(decl)
    check_function(func, global_context)
    global_context[func.name] = func


# Context:
#   set of vals (X, Y, ...)
#   set of vars (x, y, ...)
#   knowledge about vals (X + Y = 3, Y <= X, ...)
#   knowledge about vars (x -> X, y -> X + Y)
#
# Code without control structures
# - Introduce new vars at declarations
# - Introduce new vals at start for params and at function calls
# For now, ignore calls in conditions
# Handle while loops ignoring decrease and calls in cond
# - Before loop:
#   - Establish invariants
#   - Forget knowledge about vars that are assigned in loop
# - For each iteration:
#   - Introduce values for vars at start of loop
#   - Assume invariant
#   - Assume cond is true
#   - Execute body
#   - Ensure invariant holds
# - After loop has ended:
#   - Introduce values for vars after loop has ended
#   - Translate invariants to use these values
#   - Assume cond is false
# Handle while loop with call in cond
# Handle if statements
# Handle while loop decrease
