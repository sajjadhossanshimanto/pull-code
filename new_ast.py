#%%
from ast import parse, dump, iter_child_nodes
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

_GET_DEFINITION_TYPES = (ast.Try, ast.Assign) + _FOR_STMT + _FUNC_CONTAINERS + _IMPORT_STMT + _WITH_STMT
_NAME_STMT = (ast.Call, ast.Name, ast.Attribute)
_DATA_CONTAINERS = (ast.Constant, ast.List, ast.Tuple, ast.Dict, ast.Set)
_FLOW_CONTAINERS = (ast.While, ast.If)

#%%
@dataclass
class Name:
    string_name:str
    node:ast.AST
    # cache parsed defination name. if real_name exists string name is ignored.
    real_name:str = field(default=None, repr=False)# full name
    dot_lookup:set = field(default_factory=set, init=False, repr=False)

    def __post_init__(self):
        self.type_ = type(self.node)
        self.lineno = self.node.lineno
        self.end_lineno = self.node.end_lineno
        del self.node

@dataclass
class Defi_Name(Name):
    container:ast.AST = field(default=None, repr=False)

    def __post_init__(self):
        self.type_ = type(self.node)
        node = self.container or self.node
        self.lineno = node.lineno
        self.end_lineno = node.end_lineno

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
            
                    # defi_name=self.nodes[0].string_name
                    defi_parent_pos=0
                else:
                    print(f'debug: unused data type decleared at line {n.lineno} ')
                    # fixme: why not to ruturn from here
            else:
                print(f'critical : unknown defi_name type "{type(defi_name)}"')
                return 
        else:# at this point defi_name is confirmed to be string
            if defi_name not in self._pointer:
                print(f'error: {defi_name} is undefined')
                return
            defi_parent_pos=self._pointer[defi_name].me

        self.nodes.append(n)        
        # prevent use case from filter by storing 1 as RefCount
        self.rank.append(0 if is_sub_defi else 1)
        # defi_parent_pos=self._pointer[defi_name].me
        
        if n.string_name!=defi_name:# excepting direct call
            # can't use ''if n.tring_name not in self._pointer'' 
            # because of variable reassignment ( a=f(); a=5)
            self._pointer[n.string_name]=Pointer(defi_parent_pos, len(self.nodes)-1)
        self.rank[defi_parent_pos]+=1

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
            return self.nodes[pos.me], None
        
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
            return self.nodes[pos.me], var_name or None

        # print(f'error: {defi_name} is undefined.')
        return None, None

    def __getitem__(self, item) -> Union[Name, Defi_Name]:
        if item not in self._pointer:
            raise KeyError(f'item {item} is not defined. ')
        
        item = self._pointer[item].me
        return self.nodes[item]
    
    def __contains__(self, item) -> bool:
        return item in self._pointer

    def __iadd__(self, other):
        ''' for now it only transfer the defi_nodes '''
        other:DJset
        for node in other.nodes:
            if node.string_name in self._pointer:
                continue
            
            if not isinstance(node, Defi_Name):
                # i might remove this condition
                print('error')
                breakpoint()
            
            self.nodes.append(node)
            # reset for use case. as it is new defi under this scope set
            self.rank.append(0)
            pos = len(self.nodes)-1
            self._pointer[node.string_name]=Pointer(pos, pos)

    def __repr__(self) -> str:
        return str([i.string_name for i in self.nodes])

    def __bool__(self):
        return bool(self.nodes)



#%%
scope_cache: dict[str, dict[str, DJset]]
scope_cache = {}
class Scope:
    def __init__(self, nodes:Union[list, ast.AST]=None, 
        module:str = '', qual_name:str='', cache:bool=True,
        local:DJset=None, global_:DJset=None,
    ):
        if cache:
            m=scope_cache.setdefault(module, {})
            self.local = m.setdefault(qual_name, DJset())
            del m
        else:
            self.local = local or DJset()

        self.global_ = global_
        self.module = module
        self.qual_name = qual_name

        self.base_pointer = [0]
        self.todo = deque()
        self.parse(nodes)
        self.push_ebp()

    def add_use_case(self, n:Name, defi_name: str=None, is_sub_defi=False, strong_ref=True):
        if not isinstance(defi_name, str):
            self.local.add_name(n, defi_name, is_sub_defi)
        elif defi_name is None or defi_name in buitin_scope:
            self.local.add_name(n, self.local.nodes[0], is_sub_defi=is_sub_defi)
        else:
            if '.' in defi_name:
                # todo: what is the use of this condition
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

    def parsed_name(self, node: Union[ast.Call, ast.Attribute, ast.Name]) -> str:
        if type(node) is ast.Call:
            return self.parse_call(node)
        elif type(node) is ast.Attribute:
            return self.parse_attribute(node)
        elif type(node) is ast.Name:
            return node.id
        
        return node


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

    def parse_decorators(self, func_name, decorator_list:list[Union[ast.Call, ast.Name]]):
        for decorator in decorator_list:
            if isinstance(decorator, ast.Name):
                decorator=ast.Call(decorator)
                # pass function to the decorator
                decorator.args.append(func_name)
            self.parse(decorator)


    def _function_call(self, defi_node:ast.FunctionDef, call:ast.Call=None):
        ''' call executed useing local variable scope '''
        self.parse_decorators(
            defi_node.name,
            defi_node.decorator_list
        )
        self.parse_argument(defi_node.args, call)

    def _class_call(self, defi_node:ast.ClassDef, call:ast.Call=None):
        self.parse_decorators(
            defi_node.name,
            defi_node.decorator_list
        )
        
        for super_class in defi_node.bases:
            defi = self._search_defi(super_class)
            if not defi:
                print(f'error: {super_class} is undefined')
                continue

            if self.qual_name:
                qual_name = f"{self.qual_name}.{defi.string_name}"
            else:
                qual_name = defi.string_name
            
            scope = Scope(
                # ,
                qual_name=qual_name,
                module=self.module,
                global_=self.global_,
            )#
            if not scope.local:
                scope._class_call(defi.node)
            
            self.local += scope
            del scope
        
        self._class_call(defi_node, call)
        # fetch all data models
        for defi_name in self.local._pointer:
            if defi_name.startswith('__') and defi_name.endswith('__'):
                defi=self.local[defi_name]
                self._function_call(defi.node)


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
            node=Defi_Name(child.name, child, container=container)
            self.local.add_defi(node)

        elif isinstance(child, ast.Import):
            '''Import(
                    names=[
                        alias(name='a', asname='b')
                    ]
                )'''
            for alias in child.names:
                if alias.asname:
                    node=Defi_Name(alias.asname, child, alias.name, container=container)
                    self.local.add_defi(node)
                else:
                    node=Defi_Name(alias.name, child, container=container)
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
                
                node=Defi_Name(alias.name, child, container=container)
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
        if p!=self.base_pointer[-1]:
            self.base_pointer.append(p)

    def pop_ebp(self):
        return self.base_pointer.pop()


#%%
@dataclass
class Line:
    start: int
    end: int

keep_code: dict[str, list[Line]]
keep_code = {}

scanned: dict[str, set[str]]
scanned = {}
#%%
class Script:
    def __init__(self, code, relative_path) -> None:
        ast_module = parse(code)
        del code

        destination = str(relative_path)
        self.keep_line = keep_code.setdefault(destination, [])
        self.scan_list = scanned.setdefault(destination, set())
        self.globals = Scope(
            ast_module, 
            module= destination,
            cache=False
        )
        self.todo: Deque[tuple[str, ast.Call]] = deque()

    def super(self):
        # simulate super function
        pass

    def _filter(self):
        'filter empty parents'
        # position to check next. it also means pos-1 ilter(s) have been checked 
        self.globals.push_ebp()# len -1
        pos=self.globals.pop_ebp()
        stop_pos=self.globals.pop_ebp()
        
        while pos>=stop_pos and self.globals.local.nodes:
            if self.globals.local.rank[pos]==0:
                self.globals.local.nodes.pop()
                self.globals.local.rank.pop()
                pos-=1
                continue
            
            defi: Name = self.globals.local.nodes[pos]
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
            self.globals.local.rank.pop()
            self.globals.local.nodes.pop()
            pos-=1

    def add_line(self, start, end=None):
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
            
            if isinstance(defi, Name):
                self.add_line(defi.lineno, defi.end_lineno)
                continue
            elif defi.type_ is _IMPORT_STMT:
                self.add_line(defi.lineno, defi.end_lineno)
                yield defi.real_name or defi.string_name, call
                continue

            scope = Scope(
                module=self.globals.module,
                qual_name=defi.string_name,
                global_=self.globals.local,
                cache=defi.type_ is ast.ClassDef
            )
            
            self.globals.push_ebp()
            if defi.type_ is ast.ClassDef:
                scope._class_call(defi.node, call)
                if not self._contain_inside(defi.lineno, defi.end_lineno):
                    self.add_line(defi.lineno, defi.end_lineno)
            
            elif defi.type_ is ast.FunctionDef:
                scope._function_call(defi.node, call)
                self.scan_list.add(scope.string_name)
                self.add_line(defi.lineno, defi.end_lineno)
            
            self._filter()

    def __contains__(self, attr:str) -> bool:
        return attr in self.globals.local

class Project:
    def __init__(self, path: Path) -> None:
        self.root_folder = FolderIO(path)
        if not self.root_folder.exists():
            raise FileNotFoundError(path)
        
        self.script_cache={}

    def _search(self, string:str) -> tuple[FileIO, str]:
        wanted_names = string.split('.')
        root_folder = self.root_folder

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
                yield root_folder, wanted_names[pos+1:]
                return

        # yield root_folder, wanted_names[pos+1:]

    def search(self, string:str) -> tuple[Script, str]:
        for file_io, left_over in self._search(string):
            sc = self.script_cache.setdefault(
                str(file_io.path),
                Script(file_io.read(), file_io)
            )
            if left_over:
                if left_over[0] in sc:
                    yield sc, '.'.join(left_over)
            else:
                yield sc, ''

    def _custom_module(self, string:str):
        if string.startswith('.'):
            return True
        
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
destini=Path('fetched')

def copy_cat():
    for src, lines in keep_code.items():
        dst=destini.joinpath(src)
        # ensure_file
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.touch(exist_ok=True)

        with open(src) as s, open(dst, 'w') as d:
            lineno=0
            for line in lines:
                while lineno<line.start:
                    s.readline()

                for _ in range(line.end-line.start):
                    d.write(s.readline())
                d.write('\n')# a extra new line


#%%
code='''\
@bc
class A:
    @bc
    def f(a, b, c=o):
        return 1

def f():
    pass

b=A()
res=b.f()
print(res)

v=int()
'''
# code='''\
# def f(): return f
# f()()
# '''
# code='''\
# def f(): pass
# a=f()
# b=a.c()
# e=b.g()
# e
# '''
# p=parse(code)
# p=p.body
p='co.py'
l=Script(p, ['res'])
l.filter()
print(l)

#%%
#todo:  annotation=Subscript
# code='''\
# @deco
# def f(a:Union[int, str], /, b:int=3, *c, d, e=5, **k) -> int:
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
