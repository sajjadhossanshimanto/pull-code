#%%
from ast import parse, dump, iter_child_nodes, unparse
from collections import deque, namedtuple
from collections.abc import Iterable
from inspect import getfile
import ast
from itertools import chain
from pathlib import Path
from typing import Deque, TypeVar, Union
from utils import to_list, FolderIO, FileIO
from dataclasses import dataclass, field
from os.path import relpath
import os
import builtins


# for debuging and testing
iter_child_nodes=to_list(iter_child_nodes)
dumps=lambda *a, **k:print(dump(*a, **k, indent=4))

#%%
project_path = 'test_jedi'
project_path = Path(project_path)
refine_function = False
refine_class = False

#%%
# todo:
# relative imports
# simulates decorators call -> double call
# global and nonlocal keywords
# trace data types --> super tough

#%%
_FUNC_CONTAINERS=(ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
_FOR_STMT = (ast.For, ast.AsyncFor)
_IMPORT_STMT = (ast.Import, ast.ImportFrom)
_WITH_STMT = (ast.With, ast.AsyncWith)

_GET_DEFINITION_TYPES = (ast.Try, ast.Assign, ast.AnnAssign) + _FOR_STMT + _FUNC_CONTAINERS + _IMPORT_STMT + _WITH_STMT
_FLOW_CONTAINERS = (ast.While, ast.If)

_COMPREHENSIONS = (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
_DATA_CONTAINERS = (ast.Constant, ast.List, ast.Tuple, ast.Dict, ast.Set)
_NAME_STMT = (ast.Call, ast.Name, ast.Attribute) + _DATA_CONTAINERS + _COMPREHENSIONS


#%%
Scope = TypeVar('Scope')
Script = TypeVar('Script')
DJset = TypeVar('DJset')
Line = TypeVar('Line')

scope_cache: dict[str, dict[str, DJset]]
scope_cache = {}

keep_code: dict[str, list[Line]]
keep_code = {}

scanned: dict[str, set[str]]
scanned = {}


#%%
@dataclass
class Name:
    string_name:str
    node:ast.AST = field(default=None, repr=False)
    # cache parsed defination name. if real_name exists string name is ignored.
    real_name:str = field(default=None, repr=False)# full name
    dot_lookup:set = field(default_factory=set, init=False, repr=False)
    type_:ast.AST = field(default=None, init=False)

    def __post_init__(self):
        self.type_ = type(self.node)
        self.lineno = self.node.lineno
        self.end_lineno = self.node.end_lineno
        del self.node

@dataclass
class DefiName(Name):
    container:ast.AST = field(default=None, repr=False)

    def __post_init__(self):
        if not self.node:
            return 

        self.type_ = type(self.node)
        node = self.container or self.node
        self.lineno = node.lineno
        self.end_lineno = node.end_lineno

@dataclass
class Pointer:
    parent:int
    me:int

@dataclass
class Line:
    start: int
    end: int


#%%
buitin_scope = tuple(builtins.__dict__.keys())
builtins = 'builtins'
class DJset:
    def __init__(self) -> None:
        self.nodes = []
        self.rank = []# referance counter
        self.spaces = []
        self._pointer = {}# parent pointer

        self.add_defi(DefiName(builtins))

    def _find(self, defi_name, compress=False)-> Pointer:
        '''return grand parent node position'''
        parent_pos=self._pointer[defi_name]
        if parent_pos.parent==parent_pos.me:
            return parent_pos
        
        parent=self.nodes[parent_pos[0]]
        parent_pos=self._find(parent.string_name)# grand parent position
        if compress:
            self._pointer[defi_name].parent=parent_pos

        return parent_pos

    def find(self, defi_name, compress=False)-> Name:
        ''' return the grant parent ast node'''
        parent_pos=self._find(defi_name, compress)
        return self.nodes[parent_pos.me]

    def add_name(self, n:Name, defi_name: Union[str, Name], is_sub_defi=False):
        ''' if is_sub_defi is True, variable will be removed if it has no use case
            if pointed to `builtins` is only allowed via passing self.nodes[0] as defi_name
        '''
        if defi_name is None:
            print('error: defi_name can\'t be None')
            breakpoint()
        elif not isinstance(defi_name, str):
            if isinstance(defi_name, Name):
                defi_name = defi_name.string_name
                defi_parent_pos=self._pointer[defi_name].me
                if defi_parent_pos==0 and not is_sub_defi:
                    # we should not care abot buildin call( print, int, str, ...) .
                    # because they no effect on variable scope until is ot stored .
                    return

            elif isinstance(defi_name, _DATA_CONTAINERS):
                if is_sub_defi:
                    # we should not care about creading data types 
                    # until and unless is stored under a variable
                    defi_parent_pos=0
                else:
                    print(f'debug: unused data type decleared at line {n.lineno} ')
                    # fixme: why not to ruturn from here
            else:
                print(f'critical: type error for "{type(defi_name)}"')
                return 
        else:# at this point defi_name is confirmed to be string
            if defi_name not in self._pointer:
                print(f'error: {defi_name} is undefined')
                return
            defi_parent_pos=self._pointer[defi_name].me

        my_pos = self.empty_space()
        self.nodes.insert(my_pos, n)        
        # prevent use case from filter by storing 1 as RefCount
        self.rank.insert(my_pos, 0 if is_sub_defi else 1)
        # defi_parent_pos=self._pointer[defi_name].me
        
        if n.string_name!=defi_name:# excepting direct call
            # can't use ''if n.tring_name not in self._pointer'' 
            # because of variable reassignment ( a=f(); a=5)
            self._pointer[n.string_name]=Pointer(defi_parent_pos, my_pos)
        self.rank[defi_parent_pos]+=1

    def add_defi(self, defi):
        if defi.string_name in self._pointer:
            print(f'error: redefining {defi.string_name} .')
            # pre_parent_pos = self.find(defi.string_name)
            # is same as 
            pre_parent_pos = self._pointer[defi.string_name]# as defi is a defination
            pre_parent_pos = pre_parent_pos.me

            if not self.rank[pre_parent_pos]:
                self.nodes[pre_parent_pos] = defi
                return
            del pre_parent_pos

        pos=self.empty_space()
        self.nodes.insert(pos, defi)
        self.rank.insert(pos, 0)
        self._pointer[defi.string_name]=Pointer(pos, pos)

    def search(self, defi_name) -> tuple[DefiName, Union[None,  str]]:
        '''return the Defi_node for defi_name '''
        if defi_name in buitin_scope:
            return self.nodes[0], None
        
        if defi_name in self._pointer:
            pos=self._pointer[defi_name]
            return self.nodes[pos.me], None
        
        if '.' in defi_name:
            start=0
            while '.' in defi_name:
                start=defi_name.rfind('.', start)
                var_name=defi_name[start+1:]
                defi_name=defi_name[:start]
                
                if defi_name in self._pointer:
                    pos=self._pointer[defi_name].me
                elif defi_name in buitin_scope:
                    pos=0
                    var_name=None
                else: continue
                break
            else:
                # print(f'error: {defi_name} is undefined.')
                return None, None
            
            return self.nodes[pos], var_name or None

        # print(f'error: {defi_name} is undefined.')
        return None, None

    def empty_space(self):
        while self.spaces:
            pos=self.spaces.pop()
            if self.nodes[pos]: break
        else:
            pos=len(self.nodes)
        
        return pos>0 and pos or 0

    def _remove(self, pos):
        ''' unconditionaly remove node at `pos` '''
        self.nodes[pos]=self.rank[pos]=None

        if pos!=len(self.nodes)-1:
            self.spaces.append(pos)
        else:
            self.nodes.pop(pos)
            self.rank.pop(pos)
            # if self.nodes[pos]

    def __getitem__(self, item) -> Union[Name, DefiName]:
        if item not in self._pointer:
            raise KeyError(f'item {item} is not defined. ')
        
        item = self._pointer[item].me
        return self.nodes[item]

    def __contains__(self, item) -> bool:
        return item in self._pointer

    def __iadd__(self, other):
        ''' for now it only transfer the defi_nodes '''
        other:DJset
        for node_name, node_pointer in other._pointer.items():
            node=other.nodes[node_pointer.me]
            if node_name in self._pointer:
                continue
            
            if not isinstance(node, Defi_Name):
                # i might remove this condition
                print('error')
                breakpoint()
                continue
            
            pos=self.empty_space()
            self.nodes.insert(pos, node)
            # reset for use case. as it is new defi under this scope set
            self.rank.insert(pos, 0)
            self._pointer[node.string_name]=Pointer(pos, pos)
        
        return self

    def __repr__(self) -> str:
        return str([i.string_name for i in self.nodes])

    def __bool__(self):
        # the first entry is fix for builtinsp
        return len(self.nodes)>1


#%%
class Scope:
    def __init__(self, module: Script, nodes:Union[list, ast.AST]=None, 
        qual_name:str='', cache:bool=True, global_:Scope=None, scan_list:set=None
    ):
        if cache:
            m=scope_cache.setdefault(module.name, {})
            self.local = m.setdefault(qual_name, DJset())
            del m
        else:
            self.local = DJset()

        self.global_ = global_ or self
        self.module = module
        self.qual_name = qual_name
        self.full_scope = (self, self.global_)
        self.scan_list=scan_list if isinstance(scan_list, set) else set()

        # preserve all the variable for script 
        self.base_pointer = [0]
        self.todo = deque()
        self.parse(nodes)
        if nodes: self.push_ebp()

    def add_use_case(self, n:Name, defi_name: str=None, is_sub_defi=False, strong_ref=True):
        if defi_name and not isinstance(defi_name, str):
            self.local.add_name(n, defi_name, is_sub_defi)
        elif defi_name is None or defi_name in buitin_scope:
            self.local.add_name(n, self.local.nodes[0], is_sub_defi=is_sub_defi)
        else:
            if '.' in defi_name:
                n.real_name=defi_name

            defi_parent = self._search_defi(defi_name)# local search
            if defi_parent or is_sub_defi:
                self.local.add_name(n, defi_parent, is_sub_defi)
            else:
                defi_parent = self._search_defi(defi_name, self.global_)
                self.local.add_name(n, defi_parent, is_sub_defi)

    def _search_defi(self, defi_name, scope:DJset=None)-> Defi_Name:
        '''search in local if scope is not spacified'''
        scope=scope or self.local

        defi_parent, var_name = scope.search(defi_name)
        if not defi_parent: return None
        elif '.' in defi_name:
            defi_parent.dot_lookup.add(var_name)# should i append var_name or full_name

        return defi_parent

    def scope_search(self, defi_name)-> tuple[DefiName, Scope]:
        if not isinstance(defi_name, str):
            print(f'critical: type error for "{type(defi_name)}"')
            return None, None

        for scope in self.full_scope:
            if not scope.local: continue

            defi=scope._search_defi(defi_name)
            if defi: return defi, scope
        return None, None


    def parse_call(self, node:ast.Call):
        self.parse_body(node.args)
        self.parse_body(node.keywords)
        return self.parsed_name(node.func)

    def parse_attribute(self, node:ast.Attribute):
        name = self.parsed_name(node.value)
        name += f'.{node.attr}'
        return name

    def parse_comprehension(self, node:ast.comprehension, container=None):
        var_name=self.parsed_name(node.target)
        var_name=Name(var_name, container or node)

        defi=self.parsed_name(node.iter)
        self.create_local_variable(var_name, defi)
        
        self.parse_body(node.ifs)

    def parsed_name(self, node: Union[ast.Call, ast.Attribute, ast.Name]) -> str:
        if type(node) is str: pass
        elif type(node) is ast.Call:
            return self.parse_call(node)
        elif type(node) is ast.Attribute:
            return self.parse_attribute(node)
        elif type(node) is ast.Name:
            return node.id
        
        elif isinstance(node, _DATA_CONTAINERS):
            if type(node) is ast.Constant:
                pass
            elif type(node) is ast.Dict:
                self.parse_body(node.keys)
                self.parse_body(node.values)
            else:
                self.parse_body(node.elts)
            return builtins

        elif isinstance(node, _COMPREHENSIONS):
            for com in node.generators:
                self.parse_comprehension(com, node)
            
            if type(node) is ast.DictComp:
                self.parse_body((node.key, node.value))
            else:
                self.parse_body((node.elt, ))
            return builtins

        else: breakpoint()
        return node

    def parse_argument(self, argument: ast.arguments, call:ast.Call=None, fst_arg=None):
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
        call = call or ast.Call('', args=[] , keywords=[])
        if fst_arg: call.args.insert(0, fst_arg)

        pos=len(argument.defaults)-1
        defaults=argument.defaults
        while pos>=0 and defaults:# assign default values
            # siminar to zip() but in reverse manner
            var_name=argument.args[pos]
            var_name=Name(var_name.arg, var_name)

            value=self.parsed_name(defaults.pop())
            self.create_local_variable(var_name, value, 1)
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
            self.create_local_variable(var_name, value, 1)

        if argument.kwarg:
            var_name = argument.kwarg
            var_name = Name(var_name.arg, var_name)
            self.create_local_variable(var_name, is_sub_defi=1)

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
            self.create_local_variable(var_name, value, 1)

        if required_kw:
            print(f'error: missing {len(required_kw)} required keyword-only argument: {required_kw}  ')
        del required_kw


        arg_name = chain(argument.posonlyargs, argument.args)
        # filter args that is alrady passed via keyword
        arg_name = filter(lambda arg:arg.arg not in self.local, arg_name)
        arg_value = call.args
        
        if argument.vararg:
            var_name = argument.vararg
            var_name = Name(var_name.arg, var_name)

            self.create_local_variable(var_name, is_sub_defi=True)
            # same thing
            # self.create_local_variable(var_name, 'builtins', 1)

        for var in zip(arg_name, arg_value):
            var_name = var[0]
            value = var[1]

            var_name = Name(var_name.arg, var_name)
            value = self.parsed_name(value)
            self.create_local_variable(var_name, value, is_sub_defi=True)

        ## recheck and parse annotation
        # todo: points to annontations
        all_arg = chain(
            [argument.vararg, argument.kwarg],
            argument.posonlyargs,
            argument.args,
            argument.kwonlyargs,
            argument.kw_defaults
        )
        for arg in all_arg:
            if arg is None: continue
            if arg.annotation:
                self.parse_body([arg.annotation])
            
            if arg.arg in self.local: continue
            var_name = Name(arg.arg, arg)
            self.create_local_variable(var_name, is_sub_defi=True)

    def parse_decorators(self, decorator_list:list[Union[ast.Call, ast.Name]]):
        for decorator in decorator_list:
            deco_name = self.parsed_name(decorator)
            defi, scope = self.scope_search(deco_name)
            scope.do_call(defi)


    def _function_call(self, defi_node:ast.FunctionDef, call:ast.Call=None, fst_arg=None):
        ''' call executed useing local variable scope '''
        self.parse_decorators(
            defi_node.decorator_list
        )
        
        self.parse_argument(defi_node.args, call, fst_arg)
        self.parse(defi_node.body)

    def _class_call(self, defi_node:ast.ClassDef, call:ast.Call=None):
        self.parse_decorators(
            defi_node.decorator_list
        )
        
        for super_class in defi_node.bases:
            super_class=self.parsed_name(super_class)
            defi, scope = self.scope_search(super_class)
            if not defi:
                print(f'error: {super_class=} is undefined')
                continue

            self.local += scope.do_call(defi).local
        
        self.parse(defi_node.body)
        # fetch all data models
        for defi_name in self.local._pointer:
            defi=self.local[defi_name]
            if not isinstance(defi, Defi_Name):
                self.module.add_line(defi)
                continue

    def do_call(self, defi: DefiName, call:ast.Call=None, fst_arg=None)-> Scope:
        ''' return scope if defi is a classe otherwise None'''
        if defi.string_name not in self.local:
            print('error: call is not allowed outside of local scope')
            breakpoint()
            return
        
        if defi.type_ in _IMPORT_STMT:
            self.module.todo.append((defi, call))
            return

        if self.qual_name:
            qual_name = f"{self.qual_name}.{defi.string_name}"
        else:
            qual_name = defi.string_name

        scope = Scope(
            qual_name=qual_name,
            module=self.module,
            global_=self.global_,
            cache=defi.type_ is ast.ClassDef
        )
        
        self.push_ebp()
        if defi.type_ is ast.ClassDef:
            # if not loaded from cache
            if not scope.local:
                scope._class_call(defi.node, call)
                if not self.module._contain_inside(defi.lineno, defi.end_lineno):
                    self.module.add_line(defi)

        elif defi.type_ is ast.FunctionDef:
            if defi.string_name not in self.scan_list:
                self.scan_list.add(defi.string_name)
                scope._function_call(defi.node, call, fst_arg=fst_arg)
                self.module.add_line(defi)
        
        else:
            print('error: type error for call')
            # return

        # self.parse()
        self.module._filter(self)
        return scope


    def parse_withitem(self, node:ast.withitem, container=None):
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
            name_node = Name(alis, container or node, real_name = name)
        else:
            name_node = Name(name, container or node)
        
        self.add_use_case(name_node, name)

    def parse_excepthandler(self, node:ast.ExceptHandler, container=None):
        '''except Exception as e:pass
                ExceptHandler(
                    type=Name(id='Exception', ctx=Load()),
                    name='e',
                    body=[
                        Pass()])],'''
        self.todo.append(node.type)
        node=Name(node.name, container or node)

        self.add_use_case(node, self.parsed_name(node.type))
        self.parse_body(node.body, container=container)

    def create_defination(self, child, container=None):
        # todo: usef name canbe on arguments as defaults
        # self.local.add_name --> is fub_def and build_in scope
        # var_name and value
        if isinstance(child, _FUNC_CONTAINERS):
            node=DefiName(child.name, child, container=container)
            self.local.add_defi(node)

        elif isinstance(child, ast.Import):
            '''Import(
                    names=[
                        alias(name='a', asname='b')
                    ]
                )'''
            for alias in child.names:
                if alias.asname:
                    node=DefiName(alias.asname, child, real_name=alias.name, container=container)
                    self.local.add_defi(node)
                else:
                    node=DefiName(alias.name, child, container=container)
                    self.local.add_defi(node)

        elif isinstance(child, ast.ImportFrom):
            # todo: handle level
            '''from a.b import c as e, f
                ImportFrom(
                    module='a.b',
                    names=[
                        alias(name='c', asname='e'),
                        alias(name='f')]'''
            module_name = "."*child.level + child.module
            for alias in child.names:
                real_name=f'{module_name}.{alias.name}'
                if alias.asname:
                    real_name+=f'.{alias.asname}'
                
                node=DefiName(alias.name, child, real_name=real_name, container=container)
                self.local.add_defi(node)

        elif isinstance(child, _WITH_STMT):
            for withitem in child.items:
                self.parse_withitem(withitem, container = container or child)
            
            self.parse_body(child.body, container = container or child)

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
            var_name=Name(var_name, container or child)

            defi=self.parsed_name(child.iter)
            self.add_use_case(var_name, defi)

            self.parse_body(child.body, container=container or child)
            self.parse_body(child.orelse, container=container or child)
        
        elif isinstance(child, ast.Try):
            self.parse_body(child.body, container=container or child)
            for handler in child.handlers:
                self.parse_excepthandler(handler, container=container or child)
            
            self.parse_body(child.orelse, container=container or child)
            self.parse_body(child.finalbody, container=container or child)
        
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
                var_name = Name(var_name, container or child)
                self.add_use_case(var_name, value, is_sub_defi=True, strong_ref=False)

        elif isinstance(child, ast.AnnAssign):
            var_name = self.parsed_name(child.target)
            var_name = Name(var_name, container or child)
            self.add_use_case(var_name, child.value, is_sub_defi=True)
            self.parse_body([child.annotation])

        else:
            print('creatical: unknown type passed for creating variable')
            breakpoint()

    def parse(self, nodes:Union[list, ast.AST]=None):
        if nodes is not None:
            if isinstance(nodes, ast.AST):
                self.todo.append(nodes)
            elif isinstance(nodes, Iterable):
                self.todo.extend(nodes)

        while self.todo:
            child = self.todo.popleft()
            parent = None
            if isinstance(child, tuple):
                child, parent = child
            
            if type(child) in _GET_DEFINITION_TYPES:
                self.create_defination(child, container=parent)
            elif type(child) in _NAME_STMT:
                name = self.parsed_name(child)
                node = Name(name, parent or child)

                self.add_use_case(node, name)
            elif type(child) in _FLOW_CONTAINERS:
                self.parse_body(iter_child_nodes(child), child)
            else:
                self.parse_body(iter_child_nodes(child), parent)


    def parse_body(self, nodes:Iterable, container=None):
        if container:
            self.todo.extend((node, container) for node in nodes)
        else:
            self.todo.extend(nodes)

    def push_ebp(self):
        p=len(self.local.nodes)-1
        p = p>0 and p or 0
        # if p!=self.base_pointer[-1]:
        self.base_pointer.append(p)

    def pop_ebp(self):
        return self.base_pointer.pop()


#%%
class Script:
    def __init__(self, code, relative_path) -> None:
        ast_module = parse(code)
        del code

        self.name = str(relative_path)
        # only holds the function names as classes are cached
        self.scan_list = scanned.setdefault(self.name, set())
        self.keep_line = keep_code.setdefault(self.name, [])
        self.globals = Scope(
            nodes=ast_module, 
            module= self,
            scan_list=self.scan_list,
            cache=False
        )
        self.todo: Deque[tuple[str, ast.Call]] = deque()

    def super(self):
        # simulate super function
        pass

    def _filter(self, scope, preserve_main=True):
        'filter empty parents'
        scope = scope or self.globals
        # position to check next. it also means pos-1 ilter(s) have been checked 
        scope.push_ebp()# len -1
        pos=scope.pop_ebp()
        stop_pos=scope.pop_ebp()
        
        while pos>stop_pos and scope.local.nodes:
            if scope.local.rank[pos]==0:
                if not (preserve_main and stop_pos==0):
                    scope.local._remove(pos)
                pos-=1
                continue
            
            defi: Name = scope.local.nodes[pos]
            # find defi_parent node
            defi_name = defi.real_name or defi.string_name
            
            while defi.dot_lookup:
                # it is very importamt to append dot lookups 
                # first before appending defi
                attr = defi.dot_lookup.pop()
                self.todo.append((f'{defi_name}.{attr}', None))

            todo=(defi_name, None)
            if defi.type_ is ast.Call:
                todo=(defi_name, defi)

            self.todo.append(todo)
            if not (preserve_main and stop_pos==0):
                scope.local._remove(pos)
            pos-=1

    def _add_line(self, start, end=None):
        ''' start and end are both included. '''
        end=end or start
        end+=1
        l=Line(start, end)
        if not self.keep_line:
            self.keep_line.append(l)
            return
        
        for pos, line in enumerate(self.keep_line):
            if start>line.start and start>line.end:
                continue
            
            if line.start-start>1:
                self.keep_line.insert(pos, l)
            elif start>line.end:
                pos+=1
                self.keep_line.insert(pos, l)
            break
        else:
            self.keep_line.append(l)
            return
        
        l=self.keep_line[pos]
        if end>line.end:
            line.end=end
        
        pos+=1
        while pos!=len(self.keep_line):
            next_node=self.keep_line[pos]
            if end>=next_node.start:
                # marge them
                l.end=next_node.end
                self.keep_line.pop(pos)
                continue
            elif end>l.end:
                l.end=end
            
            break

    def add_line(self, name:Name):
        if not hasattr(name, 'lineno'):# for builtins
            return
        
        self._add_line(name.lineno, name.end_lineno)

    def _contain_inside(self, start, end):
        for line in self.keep_line:
            if start<=line.start<=end:
                return True
        return False

    def filter(self, name:str=None):
        '''search and filter all the requirnment under the name'''
        if name: self.todo.append((name, None))
        while self.todo:
            name, call = self.todo.popleft()
            # it is oviously guranted that there exist defi_parent
            # other wise it won't got pushed on self.globals
            defi = self.globals._search_defi(name)
            if defi.string_name in self.scan_list:
                continue

            if type(defi) is Name:
                self.add_line(defi)
                continue
            elif defi.type_ in _IMPORT_STMT:
                self.add_line(defi)
                yield defi.real_name or defi.string_name, call
                continue

            self.globals.do_call(defi, call)

    def __contains__(self, attr:str) -> bool:
        return attr in self.globals.local


#%%
# file='co.py'
# with open(file) as f:
#     s=Script(f.read(), file)
# a=s.filter('A')
# a=list(a)
# print()

#%%
class Project:
    def __init__(self, path: Path) -> None:
        self.root_folder = FolderIO(path)
        if not self.root_folder.exists():
            raise FileNotFoundError(path)
        
        self.script_cache={}

    def _search(self, string:str) -> tuple[FileIO, str]:
        if string.startswith('.'):
            level='.'
            for char in string:
                if char!='.':
                    break
                level+='.'
            
            if level>2:
                # bad practise
                print(f'error: unsupported relative import({string})')
                return
            
            root_folder=self.root_folder.join_dir(level)
        else:
            root_folder = self.root_folder

        wanted_names = string.split('.')

        for pos, child in enumerate(wanted_names):
            if not child:
                continue

            dirs, files = root_folder.list()
            if child in dirs:
                root_folder = root_folder.join_dir(child)
                init_file = root_folder.get_file('__init__.py')
                if init_file and init_file.size():
                    yield init_file, wanted_names[pos+1:]
                continue

            child+='.py'
            if child in files:
                file_io = root_folder.get_file(child)
                yield file_io, wanted_names[pos+1:]
            else:
                # yield root_folder, wanted_names[pos+1:]
                return

        # yield root_folder, wanted_names[pos+1:]

    def search(self, string:str) -> tuple[Script, str]:
        for file_io, left_over in self._search(string):
            sc = self.script_cache.setdefault(
                str(file_io.path),
                Script(
                    file_io.read(),
                    file_io.relative_path(self.root_folder)
                )
            )
            if left_over:
                if left_over[0] in sc:
                    yield sc, '.'.join(left_over)
            else:
                yield sc, ''

    def _custom_module(self, string:str):
        if string.startswith('.'):
            return True
        
        if '.' in string:
            string, _ = string.split('.', 1)
        dirs, files = self.root_folder.list()
        return string in dirs or string+'.py' in files

    def scan(self, name):
        names=[(name, None)]
        while names:
            name, call = names.pop()

            for module, name in self.search(name):
                for imp, call in module.filter(name):
                    if self._custom_module(imp):
                        names.append((imp, call))


pro = Project(project_path)
s=pro.scan('jedi.inference.filters.AnonymousFunctionExecutionFilter')
destini=Path('fetched')

def copy_cat():
    for src, lines in keep_code.items():
        if not lines: continue
        dst=destini.joinpath(src)
        # ensure_file
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.touch(exist_ok=True)

        with open(src) as s, open(dst, 'w') as d:
            lineno=1
            for line in lines:
                while lineno<line.start:
                    s.readline()
                    lineno+=1

                for _ in range(line.end-line.start):
                    t=s.readline()
                    d.write(t)
                    d.flush()
                    lineno+=1
                d.write('\n')# a extra new line
                d.flush()

os.chdir(project_path)
copy_cat()


#%%
code='''\
a=0 if 1 else 2
b= 1 and 0 or 3
'''
p=parse(code)
a=p.body[0]
b=p.body[1]