import sys

from compile import compile, CompileError

try:
  import colorama
  colorama.init()
except ImportError:
  pass


all_tests = \
[

('sum', True,
r'''
sum(x, y) -> a
  ensure a = x + y
{
  a <- x + y;
}
'''),

('max', True,
r'''
max(x, y) -> a
  ensure a >= x /\ a >= y
  ensure a = x \/ a = y
{
  if x >= y
  {
    a <- x;
  }
  else
  {
    a <- y;
  }
}
'''),

('max2', True,
r'''
max(x, y) -> a
  ensure a >= x /\ a >= y
  ensure a = x \/ a = y
{
  if x > y
  {
    a <- x - 1;
  }
  elif x = y
  {
    a <- x;
    return;
  }
  else
  {
    ensure x < y;
    a <- y - 1;
  }
  ensure x <> y;
  a <- a + 1;
}
'''),

('max3', False,
r'''
max(x, y) -> a
  ensure a >= x /\ a >= y
  ensure a = x \/ a = y
{
  if x > y
  {
    a <- x - 1;
  }
  elif x = y
  {
    a <- x;
  }
  else
  {
    a <- y - 1;
  }
  a <- a + 1;
}
'''),

('no-else', False,
r'''
foo(x) -> a
  ensure a = x
{
  if x = 1 { a <- 1; }
}
'''),

('call-conds', True,
r'''
sum(x, y) -> a
  ensure a = x + y
{
  a <- x + y;
}

foo(x, y) -> a
  require x = sum(x, y + 1)
  ensure a = -1
{
  a <- y;
}

bar(x, y) -> a
{
  if sum(x, y) = x - 1
  {
    if foo(x, y) = -1 {}
    else
    {
      ensure false;
    }
  }
}
'''),

('call-conds2', False,
r'''
sum(x, y) -> a
  ensure a = x + y
{
  a <- x + y;
}

foo(x, y) -> a
  require x = sum(x, y + 1)
  ensure a = -1
{
  a <- y;
}

bar(x, y) -> a
{
  if sum(x, y) = x
  {
    if foo(x, y) = -1 {}
    else
    {
      ensure false;
    }
  }
}
'''),

# These may not actually be correct

('_call-conj', True,
r'''
foo(x) -> a
  require x = 3
{}

bar(x) -> a
{
  if x = 3 /\ foo(x) = 0
  {}
}
'''),

('_call-disj', True,
r'''
foo(x) -> a
  require x = 3
{}

bar(x) -> a
{
  if x <> 3 \/ foo(x) = 0
  {}
}
'''),

('_call-impl', True,
r'''
foo(x) -> a
  require x = 3
{}

bar(x) -> a
{
  if x = 3 -> foo(x) = 0
  {}
}
'''),

('low-branching', True,
r'''
foo(x) -> a
  require 0 <= x <= 1
  ensure a = x
{
  if x = 0 { a <- 0; }
  if x = 1 { a <- 1; }
}
'''),

('branching-error', False,
r'''
foo(x) -> a
  require 0 <= x <= 4
  ensure a = x
{
  if x = 0 { a <- 0; }
  if x = 1 { a <- 1; }
  if x = 2 { a <- 3; }
  if x = 3 { a <- 3; }
  if x = 4 { a <- 4; }
}
'''),

('branching-call', True,
r'''
max1(x, y) -> a
  require x = 3 /\ y <= 3
  ensure a >= x /\ a >= y
  ensure a = x \/ a = y
{
  a <- 3;
}

max2(x, y) -> a
  ensure a >= x /\ a >= y
  ensure a = x \/ a = y
{
  if x <= y
  {
    a <- y;
  }
  else
  {
    a <- x;
  }
}

foo(x, y) -> a
  require x = 3
{
  if y <= x
  {
    a <- max1(x, y);
  }
  elif max2(x, y) = x
  {
    ensure false;
  }
}
'''),

('high-branching', True,
r'''
foo(x) -> a
  require 0 <= x <= 9
  ensure a = x
{
  if x = 0 { a <- 0; }
  if x = 1 { a <- 1; }
  if x = 2 { a <- 2; }
  if x = 3 { a <- 3; }
  if x = 4 { a <- 4; }
  if x = 5 { a <- 5; }
  if x = 6 { a <- 6; }
  if x = 7 { a <- 7; }
  if x = 8 { a <- 8; }
  if x = 9 { a <- 9; }
}
'''),

('scope', False,
r'''
foo(x) -> a
  require x <= 10
  ensure a = 10
{
  if x < 5
  {
    var z;
    z <- x + 1;
    x <- z;
  }
  a <- z;
}
'''),

('scope2', True,
r'''
foo(x) -> a
  require x <= 10
{
  if x < 5
  {
    var z;
    z <- x + 1;
    x <- z;
  }
  else
  {
    var z;
    z <- x - 1;
    x <- z;
  }
  a <- x;
}
'''),

('loop', True,
r'''
foo(x) -> a
  require x <= 5
  ensure a = 10
{
  while x <> 10
    ensure x <= 10
  {
    x <- x + 1;
  }
  a <- x;
}
'''),

('loop-inv-0', False,
r'''
foo(x) -> a
  require x <= 10
{
  while x <> 5
    ensure x < 5
  {
    x <- x + 1;
  }
}
'''),

('loop-inv-1', False,
r'''
foo(x) -> a
  require x < 5
{
  while x <= 5
    ensure x < 5
  {
    x <- x + 1;
  }
}
'''),

('loop2', False,
r'''
foo(x) -> a
  require x < 5
  ensure x > 5
{
  while x < 5
    ensure x <= 5
  {
    x <- x + 1;
  }
}
'''),

('loop3', False,
r'''
foo(x) -> a
  require x < 5
  ensure a >= 5
{
  a <- x;
  while a < 5
  {
    a <- a + 1;
  }
  ensure a = 5;
}
'''),

('loop4', True,
r'''
foo(x) -> a
  require x < 10
  ensure a = 10
{
  while x < 10
    ensure x <= 10
  {
    x <- x + 1;
    if x = 5
    {
      a <- 10;
      x <- 100;
      return;
    }
    ensure x <= 10;
  }
  a <- x;
}
'''),

# TODO: If this is implemented, add tests for function calls in condition
('_loop-unroll-0', True,
r'''
foo(x) -> a
{
  x <- 10;
  while x < 5
    ensure x <= 5
  {
    x <- x + 1;
  }
  ensure x = 2;
}
'''),

('mutate-param', False,
r'''
foo(x) -> a
  ensure a = x
{
  a <- 0;
  x <- 0;
}
'''),

]


def run_tests(tests):
  for name, expected, source in tests:
    if name[0] == '_':
      print('\x1b[33mSKIPPED\x1b[0m ' + name[1:])
      continue
    try:
      compile(source)
      if not expected:
        print('\x1b[31mFAILED\x1b[0m ' + name + ' (expected error but succeeded)')
        sys.exit(1)
    except CompileError as e:
      if expected:
        print('\x1b[31mFAILED\x1b[0m ' + name + ':')
        print(e.msg[:-1])
        sys.exit(1)
    print('\x1b[32mPASSED\x1b[0m ' + name)


if len(sys.argv) > 1:
  tests = []
  for name in sys.argv[1:]:
    test = [t for t in all_tests if t[0] == name]
    if len(test) == 0:
      print('No such test: ' + name)
      sys.exit(1)
    tests += test
else:
  tests = all_tests
run_tests(tests)
