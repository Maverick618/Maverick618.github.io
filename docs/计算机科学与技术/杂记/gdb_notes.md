
### gcc 编译选项
`gcc -static -g	-m32 abc.c -o abc`

static: 静态链接
g: 生成调试信息
m32: 生成32位代码
-o: 输出文件

### gdb 常用命令

#### 显示
whatis 变量名：查看变量类型或函数名
ptype：显示类型
x：进行内存查看，需要指定两个参数，第一：数据块的首地址，第二：数据块的字节数
print：显示内容
局部变量和全局变量发生冲突时，一般情况下是局部变量会隐藏全局变量，如果一个全局变量和一个函数中的局部变量同名时，如果当前停止点在函数中，用print显示出的变量的值会是函数中的局部变量的值。
info: 显示信息
show args：显示程序的参数
show environment：显示程序的环境变量


#### 函数
step：单步执行，如果遇到函数调用，会进入函数内部
finish：函数完整执行后返回
return：跳过当前函数后面的语句直接返回，返回值可以自定义，紧跟在return命令后面即可
up：向上移动一层调用栈
down：向下移动一层调用栈

#### 断点
i b(info breakpoints)：查看断点信息
disable num_1-num_n：禁用断点
enable num_1-num_n：启用断点
delete num_1-num_n：删除断点
clear：删除所有断点
clear num：删除指定断点
clear function_name：删除指定函数的断点
clear file_name:line_num：删除指定文件的指定行的断点
clear file_name：删除指定文件的所有断点
tbreak：临时断点，只在下一次执行时有效

#### 列出
l *address：查看指定地址的源代码
l symbol：查看指定符号的源代码
l function_name：查看指定函数的源代码

#### 其他
set args arg1 arg2 ...：设置程序的参数 ????这是啥
set environment var_name=value：设置环境变量
unset environment var_name：取消设置的环境变量


