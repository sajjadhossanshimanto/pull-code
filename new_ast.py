#%%
from ast import parse, dump, iter_child_nodes
from collections import deque, namedtuple
from inspect import getfile
import ast
from typing import Sequence, TypeVar, Union
import weakref
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
@dataclass
class Name:
    string_name:str
    node:ast.AST = field(default=None, repr=False)
    real_name:str = field(default=None, repr=False)# cache parsed defination name
    dot_lookup:list = field(default_factory=lambda :set(), repr=False)
    
    # def __init__(self, string_name, node) -> None:
        # self.string_name=string_name

        # self.lineno = node.lineno
        # self.end_lineno = node.end_lineno
        # self.col_offset = node.col_offset
        # self.end_col_offset = node.end_col_offset

class Defi_Name(Name):
    pass

#%%
# todo:
# asskgnment should dirently point to the defination but why !!!?
# relative imports

buitin_scope = tuple(builtins.__dict__.keys())
pointer=namedtuple('Pointer', ['parent', 'me'])

class DJset:
    def __init__(self) -> None:
        self.nodes = []
        self.rank = []# referance counter 
        self._pointer = {}# parent pointer
        # self._referance: dict[list[int]] = {}# 
        # self.trash=[]# recilean bin. for similating gc 

        self.add_defi(Defi_Name('buitins'))

    def find(self, defi_name, compress=False):
        '''return grand parent node position'''
        # I think there is no need to find grand parent
        parent_pos=self._pointer[defi_name]
        # if self.nodes[parent_pos].string_name==defi_name:
        if parent_pos.parent==parent_pos.me:
            return parent_pos[0]
        
        parent=self.nodes[parent_pos[0]]
        parent_pos=self.find(parent.string_name)
        if compress:
            self._pointer[defi_name].parent=parent_pos
        return parent_pos

    def add_name(self, n:Name, defi_name: str, is_sub_defi=False):
        ''' if is_sub_defi is True, variable will be removed if it has no use case'''
        if defi_name not in self._pointer:
            # print(f'error: {defi_name} not defined')
            if type(defi_name) is not str:
                if isinstance(defi_name, _DATA_CONTAINERS):
                    if is_sub_defi:
                        # we should not care about creading data types 
                        # until and unless is stored under a variable
                        defi_name=self.nodes[0].string_name
                    else:
                        print(f'debug: unused data type decleared at {n.node.lineno} ')
                else:
                    print(f'error : unknown defi_name type "{type(defi_name)}"')
                    return 
            else:
                if '.' in defi_name:
                    if defi_name.startswith('.'):
                        print(f'critical: unexpected relative defi_name({defi_name}) ')
                        return
                    
                    n.real_name=defi_name
                    start=0
                    while '.' in defi_name:
                        start=defi_name.rfind('.', start)
                        var_name=defi_name[start+1:]
                        defi_name=defi_name[:start]
                        
                        if defi_name in self._pointer:
                            break
                    else:
                        print(f'error: {defi_name} is undefined.')

                    # i don't know what to chose
                    if 0:
                        '''a.b.c
                            is same as
                            p.c if p=a.b is available
                            again a.b is same as
                            p.b if p=a is available

                            all except a missing p'''
                        defi_name, _, var_name=defi_name.rpartition('.')
                        # if defi_name not in self._pointer:
                            # print(f'error: {defi_name} is undefined')
                            # return

                        var_name = Name(f'{defi_name}.{var_name}', n.node)
                        self.add_name(var_name, defi_name, is_sub_defi=True)
                    
                    parent_pos=self._pointer[defi_name].me
                    parent = self.nodes[parent_pos]
                    parent.dot_lookup.add(var_name)# should i append var_name or full_name

                    del var_name, parent, parent_pos
                    
                elif defi_name in buitin_scope:
                    if is_sub_defi:
                        # we should not care abot buildin call( print, int, str, ...) .
                        # because they no effect on variable scope until is ot stored .
                        defi_name=self.nodes[0].string_name
                    else:
                        return
                else:
                    print(f'error: {defi_name} is undefined')
                    return

        self.nodes.append(n)        
        # prevent use case from filter by storing 1 as RefCount
        self.rank.append(0 if is_sub_defi else 1)
        defi_parent=self._pointer[defi_name].me
        
        if n.string_name!=defi_name:# excepting direct call
            # can't use ''if n.tring_name not in self._pointer'' 
            # because of variable reassignment ( a=f(); a=5)
            self._pointer[n.string_name]=pointer(defi_parent, len(self.nodes)-1)
        self.rank[defi_parent]+=1
        # self.rank[-1]+= 0 if is_sub_defi else 1
        # self.rank[-1]+=self.rank[defi_parent]

    def add_defi(self, defi):
        if defi.string_name in self._pointer:
            print(f'error: redefining {defi} .')
            # pre_parent_pos = self.find(defi.string_name)
            # is same as 
            pre_parent_pos = self._pointer(defi.string_name)# as defi is a defination

            if not self.rank[pre_parent_pos]:
                self.nodes[pre_parent_pos] = defi
                return
            del pre_parent_pos

        self.nodes.append(defi)
        self.rank.append(0)
        pos=len(self.nodes)-1
        self._pointer[defi.string_name]=pointer(pos, pos)

    def search(self, defi_name):
        '''return the underling ast node for defi_name as long as available '''
        if defi_name in self._pointer:
            pos=self._pointer[defi_name]
            return self.nodes[pos].node, None
        
        if '.' in defi_name:
            start=0
            while '.' in defi_name:
                start=defi_name.rfind('.', start)
                var_name=defi_name[start+1:]
                defi_name=defi_name[:start]
                
                if defi_name in self._pointer:
                    break
            else:
                print(f'error: {defi_name} is undefined.')
                return
            
            pos=self._pointer[defi_name]
            return self.nodes[pos].node, var_name

        print(f'error: {defi_name} is undefined.')

    def filter(self):# remove
        'filter empty parents'
        # position to check nex. it also means pos-1 ilter(s) have been checked 
        pos=-1# 0'th is built_in
        def remove(position):
            if self.rank[position]:
                # shouod i care about the removal of 'buildin'
                return

            if position<0 and position>pos:
                print(f'error: variable("{self.nodes[position]}") used before assignment')
                breakpoint()
            # self.rank[position]=None
            # node=self.nodes[position]
            # self.nodes[position]=None

            self.rank.pop(position)
            node=self.nodes.pop(position)

            parent_pos=self._pointer.pop(node.string_name)
            if parent_pos.parent!=parent_pos.me:# if node has a parent
                parent_pos=parent_pos[0]
                self.rank[parent_pos]-=1
                remove(parent_pos)
            return node
        
        while pos!=-len(self.rank) and self.rank:
            if not remove(pos):
                pos-=1

    def __repr__(self) -> str:
        return str([i.string_name for i in self.nodes])



#%%
_FUNC_CONTAINERS=(ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
_FOR_STMT = (ast.For, ast.AsyncFor)

_GET_DEFINITION_TYPES = (ast.Import, ast.ImportFrom, ast.withitem, ast.Assign) + _FOR_STMT + _FUNC_CONTAINERS
_NAME_STMT = (ast.Call, ast.Name, ast.Attribute)
_DATA_CONTAINERS = (ast.Constant, ast.List, ast.Tuple, ast.Dict, ast.Set)


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
        self.globals = used_names(self.module)
        self.scopes = {}
        for name in name_list:
            pass
        # before parsing for function or class call all the decorators and used names in argumwnt should be parsed 

    def search(self, name):
        scope = self.globals
        left_over = name
        if left_over:
            node, left_over = scope.search(name)


#%%
def used_names(nodes:list, local=None):
    local = local or DJset()
    if isinstance(nodes, ast.AST):
        todo = deque([nodes])
    elif isinstance(nodes, Sequence):
        todo = deque(iter_child_nodes(nodes))

    def parse_body(nodes:Sequence):
        todo.extend(nodes)


    def parse_call(node:ast.Call):
        parse_body(node.args)
        parse_body(node.keywords)
        return parsed_name(node.func)

    def parse_attribute(node:ast.Attribute):
        name = parsed_name(node.value)
        name += f'.{node.attr}'
        return name

    def parsed_name(node: Union[ast.Call, ast.Attribute, ast.Name]):
        if type(node) is ast.Call:
            return parse_call(node)
        elif type(node) is ast.Attribute:
            return parse_attribute(node)
        elif type(node) is ast.Name:
            return node.id
        
        return node

    
    def parse_withitem(node:ast.withitem):
        # todo: trace __exit__ and __start__
        '''"with a() as b"
            withitem(
                context_expr=Call(
                    func=Name(id='a', ctx=Load()),
                    args=[],
                    keywords=[]),
                optional_vars=Name(id='b', ctx=Store())),'''
        
        name = parsed_name(node.context_expr)
        if node.optional_vars:
            alis = parsed_name(node.optional_vars)
            name_node = Name(alis, node, name)
        else:
            name_node = Name(name, node)
        
        local.add_name(name_node, name)
        parse_body(node.body)

    def create_defination(child):
        # todo: usef name canbe on arguments as defaults
        # local.add_name --> is fub_def and build_in scope
        # var_name and value
        if isinstance(child, _FUNC_CONTAINERS):
            node=Defi_Name(child.name, child)
            local.add_defi(node)

        elif isinstance(child, ast.Import):
            '''Import(
                    names=[
                        alias(name='a', asname='b')
                    ]
                )'''
            for alias in child.names:
                if alias.asname:
                    node=Defi_Name(alias.asname, child, alias.name)
                    local.add_defi(node)
                else:
                    node=Defi_Name(alias.name, child)
                    local.add_defi(node)

        elif isinstance(child, ast.ImportFrom):
            # todo: handle level
            '''ImportFrom(
                module='a.c',
                names=[
                    alias(name='b')],
                level=0)'''
            pre_fix=child.module
            for alias in child.names:
                if alias.asname:
                    node=Defi_Name(alias.asname, child, f'{pre_fix}.{alias.name}')
                    local.add_defi(node)
                else:
                    node=Defi_Name(alias.name, child)
                    local.add_defi(node)

        elif isinstance(child, ast.withitem):
            parse_withitem(child)

        elif isinstance(child, _FOR_STMT):
            var_name=parsed_name(child.target)
            var_name=Name(var_name, child.target)

            node=parsed_name(child.iter)
            local.add_name(var_name, node)

            parse_body(child.body)
            parse_body(child.orelse)
        
        elif isinstance(child, ast.ExceptHandler):
            node=Name(child.name, child)
            local.add_name(node, parsed_name(child.type))
        
        elif isinstance(child, ast.Assign):
            '''Assign(
                targets=[
                    Attribute(
                        value=Name(id='a', ctx=Load()),
                        attr='b',
                        ctx=Store())],
                value=Name(id='c', ctx=Load()))'''
            
            # todo: constant value with parsed name
            value = parsed_name(child.value)
            for target in child.targets:
                var_name = parsed_name(target)
                var_name = Name(var_name, child)
                local.add_name(var_name, value, is_sub_defi=True)

    while todo:
        child=todo.popleft()
        if type(child) in _GET_DEFINITION_TYPES:
            create_defination(child)
        elif type(child) in _NAME_STMT:
            name = parsed_name(child)
            node = Name(name, child)
            local.add_name(node, name)
        else:
            todo.extend(iter_child_nodes(child))

    return local



#%%
code='''\
class A:
    def f(a, b, c=o):
        return 1
b=A()
res=b.f()
b=5
print(res)
'''
code='''\
def f(a, b, c=o):
    return 1
'''
p=parse(code)
# l=used_names(p.body)
# l.filter()
# print(l)

#%%
# # todo: ctr=load or store
# code='''
# # a(b(), c.d, k=j())
# # a.b=c
# a=[2, 3]
# '''
# p=parse(code)
# dumps(p.body[0])

# #%%
# from parso import split_lines

# split_lines(code, keepends=True)

# #%%
# d=DJset()
# d.add_defi('a')# def a(): pass
# d.add_name('b', 'a', 1)# b=a()
# # d.add_name('e', 'b')
# # d.add_name('f', 'e')
# d.add_name('()', 'a')# a()
# d.add_defi('z')
# # so filter should filter both the b and z
# d.filter()

# 