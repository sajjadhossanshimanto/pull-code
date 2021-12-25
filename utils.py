import re
from pathlib import Path


_NON_LINE_BREAKS = (
    '\v',  # Vertical Tabulation 0xB
    '\f',  # Form Feed 0xC
    '\x1C',  # File Separator
    '\x1D',  # Group Separator
    '\x1E',  # Record Separator
    '\x85',  # Next Line (NEL - Equivalent to CR+LF.
             # Used to mark end-of-line on some IBM mainframes.)
    '\u2028',  # Line Separator
    '\u2029',  # Paragraph Separator
)

def split_lines(string: str, keepends: bool = True):
    if not keepends:
        return re.split(r'\n|\r\n|\r', string)


    lst = string.splitlines(True)

    # We have to merge lines that were broken by form feed characters.
    merge = []
    for i, line in enumerate(lst):
        try:
            last_chr = line[-1]
        except IndexError:
            pass
        else:
            if last_chr in _NON_LINE_BREAKS:
                merge.append(i)

    for index in reversed(merge):
        try:
            lst[index] = lst[index] + lst[index + 1]
            del lst[index + 1]
        except IndexError:
            # index + 1 can be empty and therefore there's no need to
            # merge.
            pass

    # The stdlib's implementation of the end is inconsistent when calling
    # it with/without keepends. One time there's an empty string in the
    # end, one time there's none.
    if string.endswith('\n') or string.endswith('\r') or string == '':
        lst.append('')
    return lst

def to_list(func):
    def wraper(*args, **kwargs):
        return list(func(*args, **kwargs))
    
    return wraper



_FLOW_CONTAINERS = set(['if_stmt', 'while_stmt', 'for_stmt', 'try_stmt',
                        'with_stmt', 'async_stmt', 'suite'])
_RETURN_STMT_CONTAINERS = set(['suite', 'simple_stmt']) | _FLOW_CONTAINERS

_FUNC_CONTAINERS = set(
    ['suite', 'simple_stmt', 'decorated', 'async_funcdef']
) | _FLOW_CONTAINERS

_GET_DEFINITION_TYPES = set([
    'expr_stmt', 'sync_comp_for', 'with_stmt', 'for_stmt', 'import_name',
    'import_from', 'param', 'del_stmt', 'namedexpr_test',
])
_IMPORTS = set(['import_name', 'import_from'])


from jedi.inference.imports import load_module_from_path, load_namespace_from_path
from typing import Union
import os
from pathlib import Path


_IGNORE_FOLDERS = ('.tox', '.venv', '.mypy_cache', 'venv', '__pycache__', '.vscode')

class FileIO:
    def __init__(self, path: Union[os.PathLike, str]):
        if isinstance(path, str):
            path = Path(path)
        self.path = path

    def read(self):  # Returns bytes/str
        # We would like to read unicode here, but we cannot, because we are not
        # sure if it is a valid unicode file. Therefore just read whatever is
        # here.
        with open(self.path, 'rb') as f:
            return f.read()

    def get_parent_folder(self):
        return FolderIO(os.path.dirname(self.path))

    def get_last_modified(self):
        """
        Returns float - timestamp or None, if path doesn't exist.
        """
        try:
            return os.path.getmtime(self.path)
        except FileNotFoundError:
            return None

    def size(self):
        os.stat(self.path).st_size

    def __repr__(self):
        return '%s(%s)' % (self.__class__.__name__, self.path)

class FolderIO:
    def __init__(self, path):
        self.path = path

    def base_name(self):
        return os.path.basename(self.path)

    def get_file(self, name):
        path = os.path.join(self.path, name)
        if os.path.isfile(path):
            return FileIO(path)

    def list(self):
        _, dirs, files = next(os.walk(self.path))
        return dirs, files

    def join_dir(self, _with):
        '''return None if joined path not exists'''
        path = os.path.join(self.path, _with)
        if os.path.isdir(path):
            return FolderIO(path)

    def walk(self):
        for root, dirs, files in os.walk(self.path):
            root_folder_io = FolderIO(root)
            original_folder_ios = [FolderIO(os.path.join(root, d)) for d in dirs]
            modified_folder_ios = list(original_folder_ios)
            yield (
                root_folder_io,
                modified_folder_ios,
                [FileIO(os.path.join(root, f)) for f in files],
            )

    def __repr__(self):
        return '<%s: %s>' % (self.__class__.__name__, self.path)


class Project:
    def __init__(self, path:str) -> None:
        self.path=Path(str(path))
        self.root_folder = FolderIO(self.path)

    def search(self, string:str):
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
                return root_folder, wanted_names[pos+1:]

        # yield root_folder, wanted_names[pos+1:]

    def include(self, string:str):
        string, _ = string.split('.', 1)
        dirs, files = self.root_folder.list()
        return string in dirs or string+'.py' in files


if __name__=='__main__':
    project_path='/home/kali/Desktop/coding/pyt/clone yt/'
    seperate='firedm.cmdview.CmdView.run'

    p=Project(project_path)
    r=p.search(seperate)
    r=list(r)
    print(r)