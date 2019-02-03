import sys

from compile import compile, CompileError

try:
  import colorama
  colorama.init()
except ImportError:
  pass


tests = \
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
    a <- y - 1;
  }
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

('high-branching', True,
r'''
foo(x) -> a
  require 1 < x <= 9
  ensure a = x
{
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

]


for name, expected, source in tests:
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
