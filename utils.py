#%%
import re
import os
from pathlib import Path
from typing import Union


#%%
def to_list(func):
    def wraper(*args, **kwargs):
        return list(func(*args, **kwargs))
    
    return wraper

#%%
class FileIO:
    def __init__(self, path: Union[os.PathLike, str]):
        if isinstance(path, str):
            path = Path(path)
        self.path = path

    def read(self):
        return self.path.read_text()

    def size(self):
        return self.path.stat().st_size

    def __str__(self) -> str:
        return str(self.path)

    def __repr__(self):
        return '%s(%s)' % (self.__class__.__name__, self.path)

#%%
class FolderIO:
    def __init__(self, path):
        self.path = path

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

    def exists(self):
        return os.path.isdir(self.path)

    def __repr__(self):
        return '<%s: %s>' % (self.__class__.__name__, self.path)

