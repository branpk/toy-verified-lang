import sys

import lark
import z3


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
  print('Error at %d:%d:' % (line, column))
  print('  ' + source.split('\n')[line - 1])
  print('  ' + ' '*(column - 1) + '^')
  print(err)
  sys.exit(1)


class Function:

  def __init__(self, decl):
    self.name = decl['name'][0]
    self.params = decl['params']
    self.ret = decl['ret'][0]

    self.require = [r['cond'][0] for r in decl['reqs'].children if r.data == 'require']
    self.ensure = [r['cond'][0] for r in decl['reqs'].children if r.data == 'ensure']

    self.body = decl['body']


class LocalContext:

  def __init__(self):
    self.vals = []
    self.vars = {}
    self.knowledge = []

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


def interpret_iexpr(expr, cxt, global_context):
  if expr.data == 'ilit':
    return z3.IntVal(int(str(expr[0])))
  elif expr.data == 'ivar':
    x = str(expr[0])
    if x not in cxt.vars:
      error('Undeclared variable', expr)
    return cxt.vars[x]
  elif expr.data == 'iunop':
    i1 = interpret_iexpr(expr[1], cxt, global_context)
    return {
      '+': i1,
      '-': -i1,
    }[str(expr[0])]
  elif expr.data == 'ibinop':
    i1 = interpret_iexpr(expr[0], cxt, global_context)
    i2 = interpret_iexpr(expr[2], cxt, global_context)
    return {
      '+': i1 + i2,
      '-': i1 - i2,
    }[str(expr[1])]
  raise NotImplementedError(expr)


def interpret_bexpr(expr, cxt, global_context):
  if expr.data == 'blit':
    return z3.BoolVal({
        'true': True,
        'false': False,
      }[str(expr[0])])
  elif expr.data == 'bunop':
    if str(expr[0]) == '~':
      return z3.Not(interpret_bexpr(expr[1], cxt, global_context))
  elif expr.data == 'bbinop':
    b1 = interpret_bexpr(expr[0], cxt, global_context)
    b2 = interpret_bexpr(expr[2], cxt, global_context)
    return {
      '/\\': z3.And(b1, b2),
      '\\/': z3.Or(b1, b2),
      '->': z3.Implies(b1, b2),
      '<->': b1 == b2,
    }[str(expr[1])]
  elif expr.data == 'bicomp':
    exprs = []
    for i in range(0, len(expr.children) - 1, 2):
      i1 = interpret_iexpr(expr[i], cxt, global_context)
      i2 = interpret_iexpr(expr[i + 2], cxt, global_context)
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


def check_function(func, global_context):
  cxt = LocalContext()

  for param in func.params:
    x = param.value
    if x in cxt.vars:
      error('Variable name already used', param)
    cxt.vars[x] = cxt.new_val(x)

  for pre in func.require:
    cxt.knowledge.append(interpret_bexpr(pre, cxt, global_context))

  r = func.ret.value
  if r in cxt.vars:
    error('Variable name already used', func.ret)
  cxt.vars[r] = cxt.new_val('?' + r)
  # cxt.vars[r] = z3.IntVal(0)

  for stmt in func.body:
    if stmt.data == 'ensure':
      cxt.prove(interpret_bexpr(stmt['cond'][0], cxt, global_context), stmt)
    elif stmt.data == 'assert':
      cxt.knowledge.append(interpret_bexpr(stmt['cond'][0], cxt, global_context))
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
    else:
      raise NotImplementedError(stmt)

  for post in func.ensure:
    cxt.prove(interpret_bexpr(post, cxt, global_context), post)


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


source = r'''
sum(x, y) -> z
  ensure z = x + y
{
  z <- y + x;
}

foo(x, y) -> a
  require x = 4
  ensure a > x
{
  a <- sum(x, 3);
}
'''
ast = parser.parse(source)

global_context = {}
for decl in ast.children:
  func = Function(decl)
  check_function(func, global_context)
  print('Verified ' + func.name)
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
