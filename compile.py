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


def flatten(x):
  try:
    return sum(map(flatten, x), [])
  except:
    return [x]

def z3_and(p):
  p = flatten(p)
  if len(p) == 0:
    return z3.BoolVal(True)
  elif len(p) == 1:
    return p[0]
  else:
    return z3.And(p)


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

    self.vars_stack = []
    self.knowledge_stack = []

  def push(self):
    self.vars_stack.append(dict(self.vars))
    self.knowledge_stack.append(len(self.knowledge))

  def pop(self):
    self.vars = self.vars_stack.pop()
    old_knowledge_len = self.knowledge_stack.pop()
    new_knowledge = self.knowledge[old_knowledge_len:]
    self.knowledge = self.knowledge[:old_knowledge_len]
    return new_knowledge

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


def interpret_iexpr(expr, ctx, global_context, subst={}):
  if expr.data == 'ilit':
    return z3.IntVal(int(str(expr[0])))

  elif expr.data == 'ivar':
    x = expr[0].value
    if x in subst:
      return subst[x]
    if x not in ctx.vars:
      error('Undeclared variable', expr)
    return ctx.vars[x]

  elif expr.data == 'iunop':
    i1 = interpret_iexpr(expr[1], ctx, global_context, subst)
    return {
      '+': i1,
      '-': -i1,
    }[str(expr[0])]

  elif expr.data == 'ibinop':
    i1 = interpret_iexpr(expr[0], ctx, global_context, subst)
    i2 = interpret_iexpr(expr[2], ctx, global_context, subst)
    return {
      '+': i1 + i2,
      '-': i1 - i2,
    }[str(expr[1])]

  elif expr.data == 'icall':
    func = expr[0].value
    if func not in global_context:
      error('Undeclared function', expr)
    func = global_context[func]

    args = [interpret_iexpr(arg, ctx, global_context, subst) for arg in expr.children[1:]]
    if len(func.params) != len(args):
      error('Wrong number of arguments', expr)
    psubst = {func.params[i].value: args[i] for i in range(len(func.params))}

    for pre in func.require:
      ctx.prove(interpret_bexpr(pre, ctx, global_context, psubst), expr)

    psubst[func.ret.value] = ctx.new_val(func.name)
    for post in func.ensure:
      ctx.assume(interpret_bexpr(post, ctx, global_context, psubst))
    return psubst[func.ret.value]

  raise NotImplementedError(expr)


def interpret_bexpr(expr, ctx, global_context, subst={}):
  if expr.data == 'blit':
    return z3.BoolVal({
        'true': True,
        'false': False,
      }[str(expr[0])])

  elif expr.data == 'bunop':
    if str(expr[0]) == '~':
      return z3.Not(interpret_bexpr(expr[1], ctx, global_context, subst))

  elif expr.data == 'bbinop':
    b1 = interpret_bexpr(expr[0], ctx, global_context, subst)
    b2 = interpret_bexpr(expr[2], ctx, global_context, subst)
    return {
      '/\\': z3.And(b1, b2),
      '\\/': z3.Or(b1, b2),
      '->': z3.Implies(b1, b2),
      '<->': b1 == b2,
    }[str(expr[1])]

  elif expr.data == 'bicomp':
    exprs = []
    for i in range(0, len(expr.children) - 1, 2):
      i1 = interpret_iexpr(expr[i], ctx, global_context, subst)
      i2 = interpret_iexpr(expr[i + 2], ctx, global_context, subst)
      exprs.append({
          '=': i1 == i2,
          '<>': i1 != i2,
          '<=': i1 <= i2,
          '<': i1 < i2,
          '>=': i1 >= i2,
          '>': i1 > i2,
        }[str(expr[i + 1])])
    return z3_and(exprs)

  raise NotImplementedError(expr)


def get_top_level_blocks(stmt):
  if stmt.data == 'if':
    yield stmt['body'].children
    for branch in stmt['elifs']:
      yield branch['body'].children
    for branch in stmt['else']:
      yield branch.children
  elif stmt.data == 'while':
    yield stmt['body'].children


def get_modified_vars(stmts):
  if type(stmts) is lark.Tree:
    stmts = [stmts]

  results = set()
  for stmt in stmts:
    if stmt.data == 'assign':
      results.add(stmt['var'][0].value)
    for block in get_top_level_blocks(stmt):
      results.update(get_modified_vars(block))
  return results


def interpret_if_stmt(stmt, ctx, global_context, post):
  end_vals = {}
  for x in get_modified_vars(stmt):
    if x in ctx.vars:
      end_vals[x] = ctx.new_val('$' + x)

  def interpret_branch(cond, stmts):
    ctx.push()
    ctx.assume(cond)
    interpret_block(stmts, ctx, global_context, post)

    for x, X in end_vals.items():
      ctx.assume(X == ctx.vars[x])

    if type(cond) is list:
      cond = z3_and(cond)
    for P in ctx.pop()[1:]:
      ctx.assume(z3.Implies(cond, P))

  neg_conds = []

  cond = interpret_bexpr(stmt['cond'][0], ctx, global_context)
  interpret_branch(cond, stmt['body'].children)
  neg_conds.append(z3.Not(cond))

  for branch in stmt['elifs']:
    cond = interpret_bexpr(branch['cond'][0], ctx, global_context)
    interpret_branch(neg_conds + [cond], branch['body'].children)
    neg_conds.append(z3.Not(cond))

  if len(stmt['else'].children) > 0:
    interpret_branch(neg_conds, stmt['else'][0].children)
  else:
    interpret_branch(neg_conds, [])

  for x, X in end_vals.items():
    ctx.vars[x] = X

  # prevconds = []

  # ctx0 = ctx.push()
  # ctx0.assume(interpret_bexpr(stmt['cond'][0], ctx0, global_context))
  # interpret_block(stmt['body'].children + stmts[i+1:], ctx0, global_context, posts)
  # prevconds.append(stmt['cond'][0])

  # for branch in stmt['elifs']:
  #   ctx0 = ctx.push()
  #   for cond in prevconds:
  #     ctx0.assume(z3.Not(interpret_bexpr(cond, ctx0, global_context)))
  #   ctx0.assume(interpret_bexpr(branch['cond'][0], ctx0, global_context))
  #   interpret_block(branch['body'].children + stmts[i+1:], ctx0, global_context, posts)
  #   prevconds.append(branch['cond'][0])

  # elsebody = [] if len(stmt['else'].children) == 0 else stmt['else'][0].children
  # ctx0 = ctx.push()
  # for cond in prevconds:
  #   ctx0.assume(z3.Not(interpret_bexpr(cond, ctx0, global_context)))
  # interpret_block(elsebody + stmts[i+1:], ctx0, global_context, posts)

  # return


def interpret_while_stmt(stmt, ctx, global_context, post):
  invs = [r['cond'][0] for r in stmt['reqs'] if r.data == 'ensure']

  for inv in invs:
    ctx.prove(interpret_bexpr(inv, ctx, global_context), inv)

  for x in get_modified_vars(stmt):
    if x in ctx.vars:
      ctx.vars[x] = ctx.new_val('$' + x)

  for inv in invs:
    ctx.assume(interpret_bexpr(inv, ctx, global_context))

  cond = interpret_bexpr(stmt['cond'][0], ctx, global_context)

  ctx.push()
  ctx.assume(cond)
  interpret_block(stmt['body'].children, ctx, global_context, post)
  for inv in invs:
    ctx.prove(interpret_bexpr(inv, ctx, global_context), inv)
  ctx.pop()

  ctx.assume(z3.Not(cond))


def interpret_block(stmts, ctx, global_context, post):
  for i in range(len(stmts)):
    stmt = stmts[i]

    if stmt.data == 'ensure':
      ctx.prove(interpret_bexpr(stmt['cond'][0], ctx, global_context), stmt)

    elif stmt.data == 'assert':
      ctx.assume(interpret_bexpr(stmt['cond'][0], ctx, global_context))

    elif stmt.data == 'assign':
      x = stmt['var'][0].value
      if x not in ctx.vars:
        error('Undeclared variable', stmt['var'])
      ctx.vars[x] = interpret_iexpr(stmt['value'][0], ctx, global_context)

    elif stmt.data == 'decl':
      for var in stmt:
        x = var.value
        if x in ctx.vars:
          error('Variable name already used', var)
        ctx.vars[x] = ctx.new_val('?' + x)

    elif stmt.data == 'discard':
      interpret_iexpr(stmt['value'][0], ctx, global_context)

    elif stmt.data == 'return':
      post()
      ctx.assume(z3.BoolVal(False))

    elif stmt.data == 'if':
      interpret_if_stmt(stmt, ctx, global_context, post)

    elif stmt.data == 'while':
      interpret_while_stmt(stmt, ctx, global_context, post)

    else:
      raise NotImplementedError(stmt)


def check_function(func, global_context):
  ctx = LocalContext()

  params = {}
  for param in func.params:
    x = param.value
    if x in ctx.vars:
      error('Variable name already used', param)
    params[x] = ctx.new_val(x)
    ctx.vars[x] = params[x]

  for pre in func.require:
    ctx.assume(interpret_bexpr(pre, ctx, global_context))

  r = func.ret.value
  if r in ctx.vars:
    error('Variable name already used', func.ret)
  ctx.vars[r] = ctx.new_val('?' + r)
  # ctx.vars[r] = z3.IntVal(0)

  def check_post():
    ctx.push()
    ctx.vars = {r: ctx.vars[r]}
    ctx.vars.update(params)
    for post in func.ensure:
      ctx.prove(interpret_bexpr(post, ctx, global_context), post)
    ctx.pop()

  interpret_block(func.body.children, ctx, global_context, check_post)
  check_post()


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
