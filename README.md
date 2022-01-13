please consider the fact that this is my first time writing a markdown file

# pull-code

pull-code is a simple tool that lets you separate a specific part from a python project.
This part can either be a `class`, `function`, or `variable`.

## Use case

This can be useful where you want to use a specific feature from another project in your project. But don't want that project in your `requirnment.txt` for whatever reason.

Or you might want to learn about any specific functionality of a project and don't want to take a headache about other things.

## Features

it provides you with two main classes to determine which blocks of code need to be kept

* Project
* Script

and a helper function called `copy_cat` to copy determined line code from source to a separate place.

## Examples

suppose you have a project structure like...

* my_math
    * \_\_init\_\_.py
    * a.py
    * b.py
    * c.py

> a.py
```python
def one():
    return 1
```

> b.py
```python
pi=3.1416

def _add(a, b):
    return a+b

def _multiply(a, b):
    return a*b
```

> c.py
```python
from my_math import _add
import os

def total_sum(*__iterable):
    total=0
    for i in __iterable:
        total=_add(total, i)
    return total
```

---
from this project, you just want to separate the `total_sum` function. for that

> project_path = '.'

here we have a variable `project_path` with the path where the project located

> pro = Project(project_path)

create a `Project` object with that path

> pro.scan("my_math.b.total_sum")

with that `Project` object, you can scan for whatever functionality you want. In this example, we fill only scan for the `total_sum` function.

after the scan ends it stores all the detail in a global variable called `keep_code` that is actually a dict with file path as key and list of `Line` as value. So to copy these lines from the source there is a helper function `copy_cat` that can understand `Line`

> copy_cat(project_path)

you can also specify where to store the separated code as a 2nd argument.
by default `copy_cat` stores everything in a folder called `fetched`.

Here is the full code snippet :
```python
project_path = '.'

pro = Project(project_path)
pro.scan("my_math.b.total_sum")

copy_cat(project_path)
```
---

And the result would look like something like this.

* fetched
    * my_math
        * \_\_init\_\_.py
        * b.py
        * c.py

> b.py
```python

def _add(a, b):
    return a+b
```

> c.py
```python
from my_math import _add

def total_sum(*__iterable):
    total=0
    for i in __iterable:
        total=_add(total, i)
    return total
```
---

## Limitation

in case you have a code like this,
```python
from my_math import _add, _multiply
```
where only the `_add` function is used under `total_sum`. So after fetching, `_multiply` function is no longer exist under `b.py`

but `_multiply` is not removed from the import statement. So it might end with an `ImportError`

the reason is pull-code uses python builtin `AST` parser. while doesn't support `col_offset` for each import in a line
