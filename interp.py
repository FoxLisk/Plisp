import types
import sys
import re
import operator

default_fns = {}

for k, v in __builtins__.__dict__.items():
  if isinstance(v, (types.FunctionType, types.BuiltinFunctionType, types.MethodType, types.BuiltinMethodType, types.UnboundMethodType)):
    default_fns[k] = v

default_fns['*'] = operator.mul
default_fns['/'] = operator.truediv
default_fns['+'] = operator.add
default_fns['-'] = operator.sub
default_fns['=='] = operator.eq


class InterpretationError(Exception):
  def __init__(self, value):
    self.value = value
  def __str__(self):
    return self.value

class Context():
  def __init__(self, parent = None):
    self.params = {}
    self.parent = parent

  def has_val(self, name):
    if name in self.params:
      return True
    elif self.parent is not None:
      return self.parent.has_val(name)
    else:
      return False

  def set_val(self, name, val):
    self.params[name] = val

  def get_val(self, name):
    if name in self.params:
      return self.params[name]
    elif self.parent is not None:
      return self.parent.get_val(name)
    else:
      raise InterpretationError('Name `' + name + '` is not defined')

  def __str__(self):
    out = str(self.params)
    if self.parent is not None:
      out += '\nParent: ' + str(self.parent)
    return out

class UserFunc():
  def __init__(self, name, param_names, code, context):
    self.name = name
    self.param_names = param_names
    self.code = code
    self.creation_context = context

  def __call__(self, *args):
    #print 'calling ' + self.name 
    call_context = Context(self.creation_context)

    assignments = zip(self.param_names, args)
    for name, val in assignments:
      call_context.set_val(name, val)

    #print 'all code: ' + str(self.code)

    for tree in self.code:
      #print 'executing ' + str(tree)
      #print '  with context ' + str(call_context)
      ret = exec_tree(tree, call_context)

    return ret
    
def __defn(tree, context):
  '''
  (defn (name param..) (code))
  '''
  assert len(tree) >= 3 #(defn (name param...) (sexp))
  assert tree[0][0] == 'defn'
  args = tree[1]
  assert isinstance(tree[1], list) #args
  assert all(map(lambda tk: tk[1] == TokenType.IDENTIFIER, tree[1]))
  name = args[0][0]
  param_names = map(lambda tk: tk[0], args[1:])
  code = tree[2:]
  uf = UserFunc(name, param_names, code, context)
  context.set_val(name, uf)
  return uf

def __lambda(tree, context):
  '''
  (lambda (param..) (code))
  '''
  assert len(tree) == 3 #(defn (name param...) (sexp))
  assert tree[0][0] == 'lambda'
  args = tree[1]
  assert isinstance(tree[1], list) #args
  assert all(map(lambda tk: tk[1] == TokenType.IDENTIFIER, tree[1]))
  name = '__user_lambda_' + str(__lambda.num)
  __lambda.num += 1
  param_names = map(lambda tk: tk[0], args)
  code = tree[2:]
  uf = UserFunc(name, param_names, code, context)
  return uf

__lambda.num = 0
  
def __if(tree, context):
  '''
  (if (cond) (true) (false))
  '''
  if len(tree) < 3 or len(tree) > 4:
    raise InterpretationError('Incorrect syntax for if block')
  assert tree[0][0] == 'if'
  cond = tree[1]
  result = parse_value(cond, context)
  if result:
    return parse_value(tree[2], context)
  else:
    if len(tree) == 4:
      return parse_value(tree[3], context)

def __define(tree, context):
  '''
  (define name value)
  where value can be an arbitrary sexp or a simple value
  '''
  assert len(tree) == 3
  assert tree[0][0] == 'define'
  assert isinstance(tree[1], tuple)
  assert tree[1][1] == TokenType.IDENTIFIER
  name = tree[1][0]
  val = parse_value(tree[2], context)
  context.set_val(name, val)

interp_fns = {}
interp_fns['defn'] = __defn
interp_fns['define'] = __define
interp_fns['lambda'] = __lambda
interp_fns['if'] = __if

class TokenType:
  PAREN = 1
  IDENTIFIER = 2
  STRING = 3
  NUM = 4
  TRUE = 5
  FALSE = 6

class Parser:
  def __init__(self, tokens):
    self.tokens = tokens
    self.idx = 0

  def build_tree(self, indent = '  '):
    tree = []
    while self.idx < len(self.tokens):
      token = self.tokens[self.idx]
      self.idx += 1
      if token[1] == TokenType.PAREN:
        if token[0] == '(':
          tree.append(self.build_tree(indent + '  '))
        elif token[0] == ')':
          return tree
      else:
        tree.append(token)
    return tree

def tokenize(sexp):
  S_NUM = 1
  S_STR = 2
  S_NUL = 3
  S_IDENT = 4
  tokens = []
  buf = ''
  state = S_NUL
  i = 0
  while i < len(sexp):
    c = sexp[i]
    if state == S_NUL:
      if c.isspace():
        i += 1
      elif c == '"':
        state = S_STR
        i += 1
      elif c.isdigit():
        state = S_NUM
      elif c in '()':
        tokens.append((c, TokenType.PAREN))
        i += 1
        #state remains S_NUL
      else:
        state = S_IDENT
    elif state == S_NUM:
      if not c.isdigit():
        tokens.append((int(buf), TokenType.NUM))
        buf = ''
        state = S_NUL
      else:
        buf += c
        i += 1
    elif state == S_STR:
      if c == '"':
        tokens.append((buf, TokenType.STRING))
        buf = ''
        state = S_NUL
        i += 1
      else:
        buf += c
        i += 1
    elif state == S_IDENT:
      if c.isspace() or c in '()':
        if buf == 'true':
          tokens.append((buf, TokenType.TRUE))
        elif buf == 'false':
          tokens.append((buf, TokenType.FALSE))
        else:
          tokens.append((buf, TokenType.IDENTIFIER))
        buf = ''
        state = S_NUL
      else:
        buf += c
        i += 1
  return tokens

def is_value(expr):
  '''
  returns true if the expr is a simple value
  simple values are currently just tokens that are literals
  '''
  if not isinstance(expr, tuple):
    return False
  if expr[1] in [TokenType.NUM, TokenType.STRING, TokenType.TRUE, TokenType.FALSE]:
    return True
  return False

def get_fn(expr, context):
  if isinstance(expr, tuple):
    assert expr[1] == TokenType.IDENTIFIER
    #if it's a tuple, it's just a (foo, TokenType.IDENTIFIER)
    fn_name = expr[0]
    if context.has_val(fn_name):
      return context.get_val(fn_name)
    elif fn_name in interp_fns:
      return interp_fns[fn_name]
    elif fn_name in default_fns:
      return default_fns[fn_name]
    else:
      raise InterpretationError('Function `' + fn_name + '` not defined')
  elif isinstance(expr, list):
    print "getting func from list " + str(expr)
    if expr[0][1] == TokenType.IDENTIFIER \
      and expr[0][0] == 'lambda':
      return __lambda(expr, context)
    else:
      return exec_tree(expr, context)
  else:
    raise InterpretationError('(' + ','.join(map(lambda e: expr[0], expr)) + ') does not start with a function')

def parse_value(expr, context):
  if is_value(expr):
    if expr[1] == TokenType.TRUE:
      return True
    elif expr[1] == TokenType.FALSE:
      return False
    else:
      return expr[0]
  elif expr[1] == TokenType.IDENTIFIER:
    #grab value from context
    return context.get_val(expr[0])
  else:
    ret = exec_tree(expr, context)
    return ret

def exec_tree(tree, context):
  fn = get_fn(tree[0], context)
  if fn in interp_fns.values():
    return fn(tree, context)
  else: 
    args = map(lambda v: parse_value(v, context), tree[1:])
    return fn(*args)

file_names = sys.argv[1:]

for fn in file_names:
  f = open(fn)
  sexp = f.read()

  #filter comments
  sexp = sexp.split('\n')
  sexp = filter(lambda line: not re.match('^\s*#', line), sexp)
 
  #rejoin lines
  sexp = '\n'.join(sexp)
  tokens = tokenize(sexp)
  p = Parser(tokens)
  trees = p.build_tree()

  global_context = Context()

  for tree in trees:
    try:
      exec_tree(tree, global_context)
    except InterpretationError as e:
      print e
  f.close()
