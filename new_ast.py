#%%
from ast import parse, dump, iter_child_nodes, unparse
from collections import deque
from collections.abc import Iterable
from inspect import getfile
import ast
from itertools import chain, cycle
from pathlib import Path
from typing import TypeVar, Union
from utils import to_list, FolderIO, FileIO
from dataclasses import dataclass, field
import os
import builtins


# for debuging and testing
iter_child_nodes=to_list(iter_child_nodes)
dumps=lambda *a, **k:print(dump(*a, **k, indent=4))


#%%
_FUNC_CONTAINERS=(ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
_FOR_LOOP = (ast.For, ast.AsyncFor)
_IMPORT_STMT = (ast.Import, ast.ImportFrom)
_WITH_STMT = (ast.With, ast.AsyncWith)
_ASSIGNMENT = (ast.Assign, ast.AnnAssign)

_GET_DEFINITION_TYPES = (ast.Try, ) + _ASSIGNMENT + _FOR_LOOP + _FUNC_CONTAINERS + _IMPORT_STMT + _WITH_STMT
_OTHER_FLOW_CONTAINERS = (ast.While, ast.If)
_NON_BLOCK_TYPES = _FUNC_CONTAINERS + _IMPORT_STMT

_COMPREHENSIONS = (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
_DATA_CONTAINERS = (ast.List, ast.Tuple, ast.Dict, ast.Set)
_CONSTANT_VALUES = (ast.BoolOp, ast.Compare, ast.Constant, ast.BinOp, ast.JoinedStr)
_NAME_STMT = (ast.Call, ast.Lambda, ast.Name, ast.Attribute, ast.IfExp) + _CONSTANT_VALUES + _DATA_CONTAINERS + _COMPREHENSIONS


#%%
Scope = TypeVar('Scope')
Script = TypeVar('Script')
DJset = TypeVar('DJset')
Line = TypeVar('Line')

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
    type_:ast.AST = field(default=None, init=False)
    dot_lookup:set = field(default_factory=set, init=False, repr=False)
    extra_dependencies:set = field(default_factory=set, init=False, repr=False)

    def __post_init__(self):
        self.type_ = type(self.node)
        self.lineno = self.node.lineno
        self.end_lineno = self.node.end_lineno
        del self.node

    @classmethod
    def from_name(cls, name_obj, new_name:str=None):
        ''' it should not be used this for cloning DefiName'''
        new_name = name_obj.string_name if new_name is None else new_name
        
        node=ast.AST(lineno=name_obj.lineno, end_lineno=name_obj.end_lineno)
        node = cls(new_name, node, real_name=name_obj.real_name)

        node.dot_lookup=name_obj.dot_lookup
        node.type_=name_obj.type_

        return node

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
buitin_scope += ('__annotations__', '__builtins__', '__cached__', '__dict__', '__doc__', '__file__', '__loader__', '__name__', '__package__', '__path__', '__qualname__', '__spec__')
builtins = 'builtins_'

class DJset:
    def __init__(self) -> None:
        self.nodes = []
        self._pointer = {} # parent pointer

        self.add_defi(DefiName(builtins))

    def add_name(self, n:Name, defi_name: str)->int:
        if defi_name not in self._pointer:
            # very unlike tobe happen
            breakpoint()
            print('error: defi_name not found')
            return
        
        pos=self.empty_space()
        self.nodes.insert(pos, n)
        return pos

    def add_var(self, n: Name, defi_parent_pos: int):
        if isinstance(n.string_name, list):
            for name in n.string_name:
                name = Name.from_name(n, name)
                self.add_var(name, defi_parent_pos)
            return
        
        my_pos = self.empty_space()
        self.nodes.insert(my_pos, n)
        self._pointer[n.string_name]=Pointer(defi_parent_pos, my_pos)

    def add_defi(self, defi):
        if defi.string_name in self._pointer:
            print(f'debug: redefining {defi.string_name}')

        pos=self.empty_space()
        self.nodes.insert(pos, defi)
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
        return len(self.nodes)

    def _remove(self, pos):
        ''' unconditionaly remove node at `pos` '''
        self.nodes[pos]=None

        if pos!=len(self.nodes)-1:
            print('critical: unauthorised removal')
            breakpoint()
        else:
            self.nodes.pop(pos)

    def repos_defi(self, from_pos:int, to_pos:int):
        # this is the only case with imports
        if from_pos==to_pos: return
        defi: DefiName = self.nodes.pop(from_pos)
        self.nodes.insert(to_pos, defi)

        pointer = self._pointer[defi.string_name]
        pointer.me = pointer.parent = to_pos

    def __getitem__(self, item) -> Union[Name, DefiName]:
        if item not in self._pointer:
            raise KeyError(f'item {item} is not defined. ')
        
        item = self._pointer[item].me
        return self.nodes[item]

    def __contains__(self, item) -> bool:
        return item in self._pointer

    def __repr__(self) -> str:
        return str([i.string_name for i in self.nodes])

    def __bool__(self):
        # the first entry is fix for builtinsp
        return len(self.nodes)>1


#%%
class Scope:
    def __init__(self, module: Script, nodes:Union[list, ast.AST]=None, 
        qual_name: str = '', global_: Scope=None, local: Scope = None
    ):
        if local is not None: self.local = local
        else: self.local = DJset()

        self.script_level_scope = not bool(global_)
        self.module = module
        self.qual_name = qual_name
        self.class_name = ''# only exists for a class scope
        self.global_ = global_ or self
        self.full_scope = (self, self.global_)

        self.todo = deque()
        self.parse(nodes)

    def add_use_case(self, n: Name):
        defi_name = n.string_name
        if defi_name==builtins:
            # no need to trace use case for builtins
            return
        
        defi_parent, scope = self.scope_search(defi_name)# local search

        if not scope:
            print(f'error: {defi_name=} is undefined')
        elif scope.script_level_scope or defi_parent.type_ in _IMPORT_STMT:
            scope.local.add_name(n, defi_parent.string_name)

    def create_local_variable(self, n:Name, defi_name: str=None):
        ''' if defi_name is None points to builtins '''
        if defi_name is None:
            self.local.add_var(n, 0)
            return

        defi_parent, scope = self.scope_search(defi_name)# local search
        if not scope:
            breakpoint()
            print(f'error: {defi_name} is undefined.')
            return

        if isinstance(defi_name, str) and '.' in defi_name:
            n.real_name=defi_name
        defi_name=defi_parent.string_name

        # global scope is priorities
        if defi_name!=builtins and scope!=self:# outgoing
            pn=Name.from_name(defi_parent)
            scope.add_use_case(pn)

            self.local.nodes.append(pn)
            parent_pos=len(self.local.nodes)-1
            # self.local._pointer[defi_name]=Pointer(parent_pos, parent_pos)
        else:
            parent_pos=self.local._pointer[defi_name].me


        self.local.add_var(n, parent_pos)

    def _search_defi(self, defi_name)-> DefiName:
        '''search in local if scope is not spacified'''

        defi_parent, var_name = self.local.search(defi_name)
        if not defi_parent: return None
        elif var_name:
            defi_parent.dot_lookup.add(var_name)# should i append var_name or full_name

        return defi_parent

    def scope_search(self, defi_name)-> tuple[DefiName, Scope]:
        if not isinstance(defi_name, str):
            print(f'critical: type error for "{type(defi_name)}"')
            return None, None

        for scope in self.full_scope:
            # if not scope.local: continue

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
        if type(node) is str: return node
        elif type(node) is ast.Call:
            return self.parse_call(node)
        elif type(node) is ast.Attribute:
            return self.parse_attribute(node)
        elif type(node) is ast.Name:
            return node.id
        
        elif type(node) is ast.Lambda:
            self.parse_body(node.body)
            self.parse_argument(node.args)
            return builtins

        elif type(node) is ast.Subscript:
            # though subscript is not listed on _NAME_STMT
            self.parse_body(node.slice)
            return self.parsed_name(node.value)
        
        elif isinstance(node, _COMPREHENSIONS):
            for com in node.generators:
                self.parse_comprehension(com, node)
            
            if type(node) is ast.DictComp:
                self.parse_body((node.key, node.value))
            else:
                self.parse_body(node.elt)
            return builtins
        
        elif isinstance(node, ast.Tuple):
            if type(node.ctx) is ast.Store:
                return [self.parsed_name(i) for i in node.elts]

        elif not isinstance(node, _NAME_STMT): breakpoint()

        self.parse_body(iter_child_nodes(node))
        return builtins


    def parse_arg_list(self, arg_value_pair):
        for kw in arg_value_pair:
            var_name = kw[0]
            value = kw[1]
            
            if var_name is None: continue
            if var_name.annotation: self.parse_body([var_name.annotation])
            if var_name.arg in self.local: continue

            var_name = Name(var_name.arg, var_name)
            if value is None:
                # value can be Nonedefault kw 
                value = builtins
            else:
                value = self.parsed_name(value)
            self.create_local_variable(var_name, value)

    def parse_argument(self, argument: ast.arguments, fst_arg=None):
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
        '''
        pos=len(argument.defaults)-1
        defaults=argument.defaults
        while pos>=0 and defaults:# assign default values
            # siminar to zip() but in reverse manner
            var_name=argument.args[pos]
            var_name=Name(var_name.arg, var_name)

            value=self.parsed_name(defaults.pop())
            self.create_local_variable(var_name, value)
            pos-=1
        del pos, defaults#, value, var_name

        # set default kwargs
        self.parse_arg_list(zip(argument.kwonlyargs, argument.kw_defaults))

        # all key
        all_arg = chain(
            argument.posonlyargs,
            argument.args,
            (argument.vararg, ),
            argument.kwonlyargs,
            (argument.kwarg, )
        )
        arg_value=chain(
            fst_arg and (fst_arg, ) or tuple(),
            cycle([builtins])
        )
        self.parse_arg_list(zip(all_arg, arg_value))

    def parse_decorators(self, decorator_list:list[Union[ast.Call, ast.Name]]):
        for decorator in decorator_list:
            self.module.add_line(decorator)
            deco_name = self.parsed_name(decorator)
            defi, scope = self.scope_search(deco_name)
            scope.do_call(defi)


    def _function_call(self, defi_node:ast.FunctionDef, fst_arg=None):
        ''' call executed useing local variable scope '''
        self.parse_decorators(defi_node.decorator_list)
        self.parse_argument(defi_node.args, fst_arg)
        self.parse_body(defi_node.returns)# return annotation
        self.parse(defi_node.body)

    def _class_call(self, defi_node:ast.ClassDef):
        self.parse_decorators(defi_node.decorator_list)
        self.parse(defi_node.body)

        classes=[kw.value for kw in defi_node.keywords]
        classes+=defi_node.bases

        for super_class in classes:
            super_class=self.parsed_name(super_class)
            defi, scope = self.scope_search(super_class)
            if not defi:
                print(f'error: {super_class=} is undefined')
                continue
            
            scope.do_call(defi)

    def do_call(self, defi: DefiName, fst_arg=None)-> Scope:
        ''' return scope if defi is a classe otherwise None'''
        if defi.string_name not in self.local:
            print('error: call is not allowed outside of local scope')
            breakpoint()
            return
        elif defi.type_ in _IMPORT_STMT:
            self.module.todo.add(defi.string_name)
            return
        elif defi.string_name==builtins: return

        if self.qual_name:
            qual_name = f"{self.qual_name}.{defi.string_name}"
        else:
            qual_name = defi.string_name
        
        if qual_name in self.module.scan_list: return
        self.module.scan_list.add(qual_name)

        scope = Scope(
            qual_name=qual_name,
            module=self.module,
            global_=self.global_,
            local=None if self.script_level_scope else self.local,
        )

        self.module.add_line(defi)
        self.module.push_ebp()
        if defi.type_ is ast.ClassDef:
            scope.class_name = defi.string_name
            scope._class_call(defi.node)
        elif defi.type_ is ast.FunctionDef:
            scope._function_call(defi.node, fst_arg=fst_arg)
        else:
            print('error: type for call')

        del defi.node
        self.module._filter()


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
        
        self.create_local_variable(name_node, name)

    def parse_excepthandler(self, node:ast.ExceptHandler, container=None):
        '''except Exception as e:pass
                ExceptHandler(
                    type=Name(id='Exception', ctx=Load()),
                    name='e',
                    body=[
                        Pass()])],'''
        if node.type is None: return

        exc_type=self.parsed_name(node.type)
        if node.name is None:
            name=Name(exc_type, container or node)
            self.add_use_case(name)
        else:
            var_name=Name(node.name, container or node)
            self.create_local_variable(var_name, exc_type)
        
        self.parse_body(node.body, container=container)

    def parse_import(self, child, name_prefix='', container=None):
        for alias in child.names:
            name=alias.name
            if name_prefix:
                real_name=f'{name_prefix}.{name}'
            else:
                real_name=name

            if alias.asname:
                name=alias.asname
            defi, scope = self.scope_search(name)
            if scope and defi.type_ in _IMPORT_STMT and defi.real_name==real_name:
                continue
            del defi, scope

            node=DefiName(name, child, real_name=real_name, container=container)
            if not self.script_level_scope:
                self.global_.local.add_defi(node)
                node = Name.from_name(node)
                self.create_local_variable(node, node.string_name)
            else:
                self.local.add_defi(node)

    def create_defination(self, child, container=None):
        # todo: usef name canbe on arguments as defaults
        # self.local.add_name --> is fub_def and build_in scope
        # var_name and value
        if isinstance(child, _FUNC_CONTAINERS):
            name = child.name
            if self.class_name:
                name=f'{self.class_name}.{name}'
            
            node=DefiName(name, child, container=container)
            self.local.add_defi(node)
            if not self.script_level_scope: self.todo.append(node)

        elif isinstance(child, ast.Import):
            '''Import(
                    names=[
                        alias(name='a', asname='b')
                    ]
                )'''

            self.parse_import(child)

        elif isinstance(child, ast.ImportFrom):
            # todo: handle level
            '''from a.b import c as e, f
                ImportFrom(
                    module='a.b',
                    names=[
                        alias(name='c', asname='e'),
                        alias(name='f')]'''

            module_name = "."*child.level + child.module
            self.parse_import(child, module_name, container)

        elif isinstance(child, _WITH_STMT):
            container = container or child
            for withitem in child.items:
                self.parse_withitem(withitem, container)
            
            self.parse_body(child.body, container)

        elif isinstance(child, _FOR_LOOP):
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
            
            container=container or child
            var_name=self.parsed_name(child.target)
            var_name=Name(var_name, container)

            defi=self.parsed_name(child.iter)
            self.create_local_variable(var_name, defi)

            self.parse_body(child.body, container)
            self.parse_body(child.orelse, container)

        elif isinstance(child, ast.Try):
            container=container or child
            # reverse order as todo is a stack
            self.parse_body(child.finalbody, container)
            self.parse_body(child.orelse, container)
            
            for handler in child.handlers:
                self.parse_excepthandler(handler, container)
            self.parse_body(child.body, container)

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
                self.create_local_variable(var_name, value)

        elif isinstance(child, ast.AnnAssign):
            var_name = self.parsed_name(child.target)
            var_name = Name(var_name, container or child)

            value = child.value
            if child.value:
                value = self.parsed_name(child.value)
            self.create_local_variable(var_name, value)
            self.parse_body(child.annotation)

        else:
            print('creatical: unknown type passed for creating variable')
            breakpoint()

    def parse(self, nodes:Union[list, ast.AST]=None):
        self.parse_body(nodes)
        del nodes
        while self.todo:
            child = self.todo.popleft()
            parent = None
            if isinstance(child, tuple):
                child, parent = child

            if isinstance(child, DefiName):
                self.do_call(child)
            elif type(child) in _GET_DEFINITION_TYPES:
                self.create_defination(child, container=parent)
            elif type(child) in _NAME_STMT:
                name = self.parsed_name(child)
                node = Name(name, parent or child)

                self.add_use_case(node)
            elif type(child) in _OTHER_FLOW_CONTAINERS:
                self.parse_body(iter_child_nodes(child), parent or child)
            else:
                self.parse_body(iter_child_nodes(child), parent)


    def parse_body(self, nodes:Union[Iterable, ast.AST], container=None):
        if not nodes: return
        
        if isinstance(nodes, ast.AST):
            if container:
                self.todo.appendleft((nodes, container))
            else:
                self.todo.appendleft(nodes)
        elif isinstance(nodes, Iterable):
            if container:
                nodes = [(node, container) for node in nodes]
            
            pos=len(nodes)-1
            while pos>=0:
                self.todo.appendleft(nodes[pos])
                pos-=1


#%%
class Script:
    def __init__(self, code, relative_path) -> None:
        ast_module = parse(code)
        del code

        self.todo: set[str] = set()
        self.name = str(relative_path)
        # only holds the function names as classes are cached
        self.scan_list = scanned.setdefault(self.name, set())
        self.keep_line = keep_code.setdefault(self.name, [])
        # preserve all the variable for script 
        self.base_pointer = [0]
        self.imports = set()

        self.globals = Scope(module=self)
        for node in iter_child_nodes(ast_module):
            if isinstance(node, _NON_BLOCK_TYPES):
                self.globals.parse(node)
            
            elif isinstance(node, _ASSIGNMENT):
                self.push_ebp()
                self.globals.parse(node)
                self.push_ebp()
                start=self.pop_ebp()
                stop=self.pop_ebp()

                veriables: list[Name] = []
                target = isinstance(node, ast.Assign) and len(node.targets) or 1
                for _ in range(target):
                    stop+=1
                    veriables.append(self.globals.local.nodes[stop])

                dependent=[]
                for pos in range(start, stop, -1):
                    node = self.globals.local.nodes[pos]
                    dependent.append(node.string_name)

                for var in veriables:
                    var.extra_dependencies.update(dependent)

            else:
                self.push_ebp()
                self.globals.parse(node)
                self.add_line(node)
                self._filter(True)

        self.filter()
        self.push_ebp()

    def _filter(self, preserve_main=False):
        'filter empty parents'
        scope = self.globals
        # position to check next. it also means pos-1 ilter(s) have been checked 
        self.push_ebp()# len -1
        pos=self.pop_ebp()
        stop_pos=self.pop_ebp()

        while pos>stop_pos and scope.local.nodes:
            defi: Name = scope.local.nodes[pos]
            # find defi_parent node
            defi_name = defi.string_name

            if not defi.dot_lookup:
                self.todo.add(defi_name)
            while defi.dot_lookup:
                # it is very importamt to append dot lookups 
                # first before appending defi
                attr = defi.dot_lookup.pop()
                self.todo.add(f'{defi_name}.{attr}')

            if not preserve_main:
                # do not remove root level definations
                if isinstance(defi, DefiName) and defi.type_ in _IMPORT_STMT:
                    stop_pos+=1
                    scope.local.repos_defi(pos, stop_pos)
                    continue

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
            
            if line.start-start>=1:
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

    def push_ebp(self):
        p=len(self.globals.local.nodes)-1
        p = p>0 and p or 0
        # if p!=self.base_pointer[-1]:
        self.base_pointer.append(p)

    def pop_ebp(self):
        return self.base_pointer.pop()

    def filter(self, name:str=None):
        '''search and filter all the requirnment under the name'''
        if name: self.todo.add(name)
        while self.todo:
            name = self.todo.pop()
            # it is oviously guranted that there exist defi_parent
            # other wise it won't got pushed on self.globals
            defi = self.globals._search_defi(name)
            if defi.string_name in self.scan_list:
                continue

            self.add_line(defi)
            if type(defi) is Name:
                # variable
                self.scan_list.add(defi.string_name)
                self.todo.update(defi.extra_dependencies)
                pointer = self.globals.local._pointer[defi.string_name]
                defi_parent = self.globals.local.nodes[pointer.parent]
                self.todo.add(defi_parent.string_name)

            elif defi.type_ in _IMPORT_STMT:
                defi_name = defi.real_name or defi.string_name
                if defi.dot_lookup:
                    while defi.dot_lookup:
                        func=defi.dot_lookup.pop()
                        self.imports.add(f'{defi_name}.{func}')
                    del func
                else:
                    self.imports.add(defi_name)
            else:
                self.globals.do_call(defi)
        return

    def __contains__(self, attr:str) -> bool:
        return attr in self.globals.local


#%%
# path = 'test_jedi/jedi/inference/compiled/access.py'
# with open(path) as f:
#     s=Script(f.read(), '.')

# s.filter('get_api_type')
# print(keep_code)

# exit()
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
            if not child: continue

            dirs, files = root_folder.list()
            if child in dirs:
                root_folder = root_folder.join_dir(child)
                init_file = root_folder.get_file('__init__.py')
                if init_file and init_file.size():
                    yield init_file, wanted_names[pos+1:]
                continue

            child += '.py'
            if child in files:
                file_io = root_folder.get_file(child)
                yield file_io, wanted_names[pos+1:]
            else:
                # yield root_folder, wanted_names[pos+1:]
                return

        # yield root_folder, wanted_names[pos+1:]

    def search(self, string:str) -> tuple[Script, str]:
        possible_files=[]
        init_files=[]
        for mdl in self._search(string):
            # whatever yielded late is much deeper match
            if mdl[0].name == '__init__.py':
                init_files.insert(0, mdl)
            else:
                possible_files.insert(0, mdl)

        if not (possible_files or init_files):
            print(f'error: module({string}) not found ')
            return

        for file_io, left_over in chain(possible_files, init_files):
            path=str(file_io.path)
            if path in self.script_cache:
                sc = self.script_cache[path]
            else:
                sc = Script(
                    file_io.read(),
                    file_io.relative_path(self.root_folder)
                )
                self.script_cache[path] = sc

            if left_over:
                if left_over[0] in sc:
                    return sc, '.'.join(left_over)
            else:
                breakpoint()
                'that means we needs to keep the whole file'
                return sc, ''

    def _custom_module(self, string:str):
        if string.startswith('.'):
            return True
        
        if '.' in string:
            string, _ = string.split('.', 1)
        dirs, files = self.root_folder.list()
        return string in dirs or string+'.py' in files

    def scan(self, name):
        names=set([name])
        while names:
            name = names.pop()

            module, name = self.search(name)
            module.filter(name)
            while module.imports:
                imp=module.imports.pop()
                print(imp)
                if self._custom_module(imp):
                    names.add(imp)


project_path = 'test_jedi'
project_path = Path(project_path)

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

# %%
