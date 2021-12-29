#%%
from ast import parse, dump, iter_child_nodes
from collections import deque, namedtuple
from collections.abc import Iterable
from inspect import getfile
import ast
from itertools import chain
from typing import Deque, TypeVar, Union
from utils import split_lines, to_list
from dataclasses import dataclass, field
from os.path import relpath
import builtins

# for debuging and testing
iter_child_nodes=to_list(iter_child_nodes)
dumps=lambda *a, **k:print(dump(*a, **k, indent=4))

#%%
project_path='/home/kali/Desktop/coding/pyt/clone yt/'


#%%
# todo:
# asskgnment should dirently point to the defination but why !!!?
# relative imports
# todo: trace __exit__ and __enter__
# simulates decorators call -> double call
# global and nonlocal keywords
# trace data types --> super tough

#%%
_FUNC_CONTAINERS=(ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
_FOR_STMT = (ast.For, ast.AsyncFor)
_IMPORT_STMT = (ast.Import, ast.ImportFrom)

_GET_DEFINITION_TYPES = (ast.withitem, ast.ExceptHandler, ast.Assign) + _FOR_STMT + _FUNC_CONTAINERS + _IMPORT_STMT
_NAME_STMT = (ast.Call, ast.Name, ast.Attribute)
_DATA_CONTAINERS = (ast.Constant, ast.List, ast.Tuple, ast.Dict, ast.Set)

#%%
@dataclass
class Name:
    string_name:str
    node:ast.AST = field(default=None, repr=False)
    # cache parsed defination name. if real_name exists string name is ignored.
    real_name:str = field(default=None, repr=False)# full name
    dot_lookup:list = field(default_factory=lambda :set(), repr=False)

@dataclass
class Defi_Name(Name):
    return_type: list = field(default_factory=lambda :[], init=False, repr=None)

@dataclass
class Pointer:
    parent:int
    me:int

buitin_scope = tuple(builtins.__dict__.keys())
class DJset:
    def __init__(self) -> None:
        self.nodes = []
        self.rank = []# referance counter 
        self._pointer = {}# parent pointer

        self.add_defi(Defi_Name('builtins'))

    def _find(self, defi_name, compress=False)-> Pointer:
        '''return grand parent node position'''
        parent_pos=self._pointer[defi_name]
        if parent_pos.parent==parent_pos.me:
            return parent_pos[0]
        
        parent=self.nodes[parent_pos[0]]
        parent_pos=self._find(parent.string_name)
        if compress:
            self._pointer[defi_name].parent=parent_pos
        return parent_pos

    def find(self, defi_name, compress=False)-> ast.AST:
        ''' return the grant parent ast node'''
        parent_pos=self._find(defi_name, compress)
        return self.nodes[parent_pos.me]

    def add_name(self, n:Name, defi_name: str=None, is_sub_defi=False):
        ''' if is_sub_defi is True, variable will be removed if it has no use case
            if defi_name is None `n` will be pointed to `builtins`
        '''
        if defi_name is None:
            defi_name=self.nodes[0].string_name
            if n.string_name==defi_name:
                # we should not care abot buildin call( print, int, str, ...) .
                # because they no effect on variable scope until is ot stored .
                return
        elif not isinstance(defi_name, str):
            if isinstance(defi_name, _DATA_CONTAINERS):
                if is_sub_defi:
                    # we should not care about creading data types 
                    # until and unless is stored under a variable
                    defi_name=self.nodes[0].string_name
                else:
                    print(f'debug: unused data type decleared at line {n.node.lineno} ')
            else:
                print(f'critical : unknown defi_name type "{type(defi_name)}"')
                return 
        elif defi_name not in self._pointer:
            # print(f'error: {defi_name} not defined')
            print(f'critical: attemping undefined : {defi_name} ')
            return


        self.nodes.append(n)        
        # prevent use case from filter by storing 1 as RefCount
        self.rank.append(0 if is_sub_defi else 1)
        defi_parent=self._pointer[defi_name].me
        
        if n.string_name!=defi_name:# excepting direct call
            # can't use ''if n.tring_name not in self._pointer'' 
            # because of variable reassignment ( a=f(); a=5)
            self._pointer[n.string_name]=Pointer(defi_parent, len(self.nodes)-1)
        self.rank[defi_parent]+=1

    def add_defi(self, defi):
        if defi.string_name in self._pointer:
            print(f'error: redefining {defi} .')
            # pre_parent_pos = self.find(defi.string_name)
            # is same as 
            pre_parent_pos = self._pointer(defi.string_name)# as defi is a defination
            pre_parent_pos = pre_parent_pos.me

            if not self.rank[pre_parent_pos]:
                self.nodes[pre_parent_pos] = defi
                return
            del pre_parent_pos

        self.nodes.append(defi)
        self.rank.append(0)
        pos=len(self.nodes)-1
        self._pointer[defi.string_name]=Pointer(pos, pos)

    def search(self, defi_name) -> tuple[Defi_Name, Union[None,  str]]:
        '''return the Defi_node for defi_name '''
        if defi_name in self._pointer:
            pos=self._pointer[defi_name]
            return self.nodes[pos.me].node, None
        
        if '.' in defi_name:
            start=0
            while '.' in defi_name:
                start=defi_name.rfind('.', start)
                var_name=defi_name[start+1:]
                defi_name=defi_name[:start]
                
                if defi_name in self._pointer:
                    break
            else:
                # print(f'error: {defi_name} is undefined.')
                return None, None
            
            pos=self._pointer[defi_name]
            return self.nodes[pos].node, var_name or None

        # print(f'error: {defi_name} is undefined.')
        return None, None

    def __getitem__(self, item):
        if item not in self._pointer:
            raise KeyError(f'item {item} is not defined. ')
        
        item = self._pointer[item].me
        return self.nodes[item]
    
    def __contains__(self, item):
        return item in self._pointer

    def __repr__(self) -> str:
        return str([i.string_name for i in self.nodes])



#%%
class Scope:
    def __init__(self, nodes:Union[list, ast.AST]=None, 
        local:DJset=None, global_:DJset=None, type_:str = 'function'
    ):
        self.local = local or DJset()
        self.global_ = global_
        self.type = type_ # 'module'| 'function' | 'class'
        self.base_pointer = [0]

        self.todo = deque()
        self.parse(nodes)
        self.push_ebp()

    def add_use_case(self, n:Name, defi_name: str=None, is_sub_defi=False, strong_ref=True):
        if not isinstance(defi_name, str):
            self.local.add_name(n, defi_name, is_sub_defi)
        elif defi_name in buitin_scope or defi_name is None:
            self.local.add_name(n, is_sub_defi=is_sub_defi)
        elif is_sub_defi:
            self.local.add_name(n, defi_name, is_sub_defi)
        else:
            if '.' in defi_name:
                # todo: what is the use of this condition
                n.real_name=defi_name

            defi_parent, scope = self._search_scope(defi_name)
            if defi_parent:
                if strong_ref:
                    nonlocal_=self.global_+self.local
                    Scope(
                        global_=self.global_
                    )
                
                    scope.add_name(n, defi_name, is_sub_defi)
            else:
                print(f'error: {defi_name} is undefined')

    def _search_defi(self, defi_name, scope:DJset)-> Defi_Name:
        if defi_name.startswith('.'):
            print(f'critical: unexpected syntax error -> defi_name({defi_name}) ')
            return False

        defi_parent, var_name = scope.search(defi_name)
        if not defi_parent: return None
        elif '.' in defi_name:
            defi_parent.dot_lookup.add(var_name)# should i append var_name or full_name

        return defi_parent


    def parse_call(self, node:ast.Call):
        self.parse_body(node.args)
        self.parse_body(node.keywords)
        return self.parsed_name(node.func)

    def parse_attribute(self, node:ast.Attribute):
        name = self.parsed_name(node.value)
        name += f'.{node.attr}'
        return name

    def parsed_name(self, node: Union[ast.Call, ast.Attribute, ast.Name]):
        if type(node) is ast.Call:
            return self.parse_call(node)
        elif type(node) is ast.Attribute:
            return self.parse_attribute(node)
        elif type(node) is ast.Name:
            return node.id
        
        return node


    #%%
    def parse_argument(self, argument: ast.arguments, call:ast.Call=None):
        ''' 
            def f(a:int, /, b:int=3, *c, d, e=5, **k): pass
                arguments(
                    posonlyargs=[
                        arg(
                            arg='a',
                            annotation=Name(id='int', ctx=Load()))],
                    args=[
                        arg(
                            arg='b',
                            annotation=Name(id='int', ctx=Load()))],
                    vararg=arg(arg='c'),
                    kwonlyargs=[
                        arg(arg='d'),
                        arg(arg='e')],
                    kw_defaults=[
                        None,
                        Constant(value=5)],
                    kwarg=arg(arg='k'),
                    defaults=[
                        Constant(value=3)])

            f(f, 2, 3, 4, thread=1)
                Call(
                    func=Name(id='f', ctx=Load()),
                    args=[
                        Name(id='f', ctx=Load()),
                        Constant(value=2),
                        Constant(value=3),
                        Constant(value=4)],
                    keywords=[
                        keyword(
                            arg='thread',
                            value=Constant(value=1))])
        '''
        # todo: points to annontations
        # parse annotation
        all_arg = chain(
            [argument.vararg, argument.kwarg],
            argument.posonlyargs,
            argument.args,
            argument.kwonlyargs,
            argument.kw_defaults
        )
        for arg in all_arg:
            # todo: instade of directly pointing to the builtins
            # it would be better if i could point it to the spacified
            # annotation. but for thag i might need to point to a data type
            # tuple[int, func] or point to two different types at the same time
            # Union[func, func2]. for the simplisity keep it for later
            var_name = Name(arg.arg, arg)
            self.add_use_case(var_name)

            self.parse_body(arg.annotation)
        del arg, all_arg

        call = call or ast.Call('', args=[], keywords=[])

        pos=len(argument.defaults)-1
        defaults=argument.defaults
        while pos>=0 and defaults:# assign default values
            # siminar to zip() but in reverse manner
            var_name=argument.args[pos]
            var_name=Name(var_name.arg, var_name)

            value=self.parsed_name(defaults.pop())
            self.add_use_case(var_name, value, 1, strong_ref=True)
            pos-=1
        del pos, defaults#, value, var_name

        # set default kwargs
        required_kw=set()
        for kw in zip(argument.kwonlyargs, argument.kw_defaults):
            var_name = kw[0]
            value = kw[1]
            if value is None:
                required_kw.add(var_name.arg)
                continue
            
            var_name = Name(var_name.arg, var_name)
            value = self.parsed_name(value  )
            self.add_use_case(var_name, value, 1, strong_ref=False)

        if argument.kwarg:
            var_name = argument.kwarg
            var_name = Name(var_name.arg, var_name)
            self.add_use_case(var_name)

        # kwargs passed on function
        available_kw=list(arg.arg for arg in chain(argument.args, argument.kwonlyargs))
        for kw in call.keywords:
            var_name = Name(kw.arg, kw)
            if kw.arg in available_kw:
                if kw.arg in required_kw:
                    required_kw.remove(kw.arg)
                # no proablem if not a reqjired keywork
            else:
                if not argument.kwarg:
                    print(f'error: passed an unexpected keyword argument "{kw.arg}" ')
                continue

            value = self.parsed_name(kw.value)
            self.add_use_case(var_name, value, 1, strong_ref=False)

        if required_kw:
            print(f'error: missing {len(required_kw)} required keyword-only argument: {required_kw}  ')
        del required_kw


        arg_name = chain(argument.posonlyargs, argument.args)
        # filter args that is alrady passed via keyword
        arg_name = filter(lambda arg:arg.arg not in self.local, arg_name)
        arg_name = list(arg_name)
        arg_value = call.args
        
        if not argument.vararg:
            if len(arg_value)>len(arg_name):
                print(f'error: expected {len(arg_value)} values but {len(arg_name)} were provided ')
            elif len(arg_value)<len(arg_name):
                print(f'error: missing {len(arg_name)-len(arg_value)} required positional argument ')
        else:
            var_name = argument.vararg
            var_name = Name(var_name.arg, var_name)

            self.add_use_case(var_name)
            # same thing
            # self.add_use_case(var_name, 'builtins', 1)

        for var in zip(arg_name, arg_value):
            var_name = var[0]
            value = var[1]

            var_name = Name(var_name.arg, var_name)
            value = self.parsed_name(value)
            self.add_use_case(var_name, value, is_sub_defi=True)

    def _function_call(self, defi_node:ast.AST, call:ast.Call=None):
        ''' call executed useing local variable scope '''
        for decorator in defi_node.decorator_list:
            # scope, defi = self._search_scope(self.parsed_name(decorator))
            if isinstance(decorator, ast.Name):
                decorator=ast.Call(decorator)
                # pass function to the decorator
                decorator.args.append(call.func)
            self.parse(decorator)

        del decorator
        
        
        self.parse_argument(defi_node, call)


    def parse_withitem(self, node:ast.withitem):
        '''"with a() as b"
            withitem(
                context_expr=Call(
                    func=Name(id='a', ctx=Load()),
                    args=[],
                    keywords=[]),
                optional_vars=Name(id='b', ctx=Store())),'''
        
        name = self.parsed_name(node.context_expr)
        if node.optional_vars:
            alis = self.parsed_name(node.optional_vars)
            name_node = Name(alis, node, name)
        else:
            name_node = Name(name, node)
        
        self.add_use_case(name_node, name)            

    def create_defination(self, child):
        # todo: usef name canbe on arguments as defaults
        # self.local.add_name --> is fub_def and build_in scope
        # var_name and value
        if isinstance(child, _FUNC_CONTAINERS):
            node=Defi_Name(child.name, child)
            self.local.add_defi(node)

        elif isinstance(child, ast.Import):
            '''Import(
                    names=[
                        alias(name='a', asname='b')
                    ]
                )'''
            for alias in child.names:
                if alias.asname:
                    node=Defi_Name(alias.asname, child, alias.name)
                    self.local.add_defi(node)
                else:
                    node=Defi_Name(alias.name, child)
                    self.local.add_defi(node)

        elif isinstance(child, ast.ImportFrom):
            # todo: handle level
            '''from a.b import c as e, f
                ImportFrom(
                    module='a.b',
                names=[
                        alias(name='c', asname='e'),
                        alias(name='f')]'''
            module_name=child.module
            for alias in child.names:
                real_name=f'{module_name}.{alias.name}'
                if alias.asname:
                    real_name+=f'.{alias.asname}'
                
                    node=Defi_Name(alias.name, child)
                    self.local.add_defi(node)

        elif isinstance(child, ast.withitem):
            self.parse_withitem(child)

        elif isinstance(child, _FOR_STMT):
            ''' for i in range(1): pass
                else: pass
                    
                For(
                    target=Name(id='i', ctx=Store()),
                    iter=Call(
                        func=Name(id='range', ctx=Load()),
                        args=[
                            Constant(value=1)],
                        keywords=[]),
                    body=[
                        Pass()],
                    orelse=[
                        Pass()])],'''
            var_name=self.parsed_name(child.target)
            var_name=Name(var_name, child.target)

            defi=self.parsed_name(child.iter)
            self.add_use_case(var_name, defi)

            self.parse_body(child.body)
            self.parse_body(child.orelse)
        
        elif isinstance(child, ast.ExceptHandler):
            '''except Exception as e:pass
                ExceptHandler(
                    type=Name(id='Exception', ctx=Load()),
                    name='e',
                    body=[
                        Pass()])],'''
            self.todo.append(child.type)
            node=Name(child.name, child)

            self.add_use_case(node, self.parsed_name(child.type))
            self.parse_body(child.body)
        
        elif isinstance(child, ast.Assign):
            '''Assign(
                targets=[
                    Attribute(
                        value=Name(id='a', ctx=Load()),
                        attr='b',
                        ctx=Store())],
                value=Name(id='c', ctx=Load()))'''
            
            # todo: constant value with parsed name
            value = self.parsed_name(child.value)
            for target in child.targets:
                var_name = self.parsed_name(target)
                var_name = Name(var_name, child)
                self.add_use_case(var_name, value, is_sub_defi=True, strong_ref=False)

        else:
            print('creatical: unknown type passed for creating variable')
            breakpoint()

    def parse(self, nodes:Union[list, ast.AST]):
        if nodes is None:
            return 
        elif isinstance(nodes, ast.AST):
            self.todo.append(nodes)
        elif isinstance(nodes, Iterable):
            self.todo.extend(nodes)

        while self.todo:
            child = self.todo.popleft()
            if type(child) in _GET_DEFINITION_TYPES:
                self.create_defination(child)
            elif type(child) in _NAME_STMT:
                name = self.parsed_name(child)
                node = Name(name, child)

                self.add_use_case(node, name)
            else:
                self.todo.extend(iter_child_nodes(child))


    def parse_body(self, nodes:Iterable):
        self.todo.extend(nodes)

    def push_ebp(self):
        p=len(self.local)
        if p!=self.base_pointer:
            self.base_pointer.append(p)

    def pop_ebp(self):
        return self.base_pointer.pop()
    

#%%
class Script:
    def __init__(self, file, name_list) -> None:
        # self.file=file
        with open(file) as f:
            code = f.read()
        
        self.line_code = split_lines(code)
        self.module = parse(code)
        del code

        self.defination = relpath(file, project_path)
        self.globals = Scope(self.module)
        self.type_object = {} # cache class scope
        self.scanned=set()
        
        for name in name_list:#
            pass
        # before parsing for function or class call all the decorators and used names in argumwnt should be parsed 

    def create_scope(self, call: ast.Call, defi_node: Defi_Name, scope: Scope = None):
        defi_name = defi_node.string_name
        if defi_node in self.scopes:
            return self.scopes[defi_name]

        defi_node = defi_node.node
        scope = scope or Scope()

        for decorator in defi_node.decorator_list:
            if isinstance(decorator, ast.Name):
                decorator=ast.Call(decorator)
            scope.parse(decorator)
        del decorator


        if isinstance(defi_node, ast.FunctionDef):
            scope.parse(defi_node)
        
        elif isinstance(defi_node, ast.ClassDef):
            inharits=deque(defi_node.bases)
            while inharits:
                super_class = inharits.popleft()

                node, left_over = self.globals.search(super_class)
                if left_over or not node:
                    print(f'critical: super class({super_class}) search error. ')
                    # might not defined
                    breakpoint()

                self.create_scope(super_class, node, local=scope)


            scope.parse(defi_node, local=scope)
            # search for init
            scope.parse(, )
        else:
            print(f"error: can't create scope for {defi_node} ")
            return

        self.scopes[]
        return scope

    def scan(self):
        pass

    def super(self):
        pass

    def search(self, name):
        # search among class can be complecated 
        scope = self.globals
        left_over = name
        if left_over:
            node, left_over = scope.search(name)



#%%
code='''\
@bc
class A:
    @bc
    def f(a, b, c=o):
        return 1

b=A()
res=b.f()
print(res)
'''

with open('co.py') as f:
    code=f.read()

p=parse(code)
p=p.body

l=Scope(p)
# l.filter()
print(l)

#%%
# code='''\
# @deco
# def f(a:int, /, b:int=3, *c, d, e=5, **k) -> int:
#     pass
# f(1, 2, 3, 4, thread=1)
# '''
# p=parse(code)
# argument=p.body[0].args
# call=p.body[1].value

# l=Scope([argument, call])

#%%
# # todo: ctr=load or store
# code='''
# # a(b(), c.d, k=j())
# # a.b=c
# a=[2, 3]
# '''
# p=parse(code)
# dumps(p.body[0])

#%%
