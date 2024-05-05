## Running Coq 运行 Coq
Every time a new shell is opened one has to type in the following lines in order to use Coq
每次打开新外壳时，都必须输入以下行才能使用 Coq

export OPAMROOT=~/opam-coq.8.9.0
eval `opam config env`
After that coqc -v shall run and print the version of Coq.
之后 coqc -v ，应运行并打印 Coq 版本。

实测`opam config env`好使，然后就可以进行coq的命令了，包括`coq_makefile -f _CoqProject *.v -o Makefile`

## windows 下 CoqProject
安装好coq后，需要配置环境变量，然后重启电脑以刷新环境变量。

## 编译缓存 链接（.vo）
!!! note "Software Foundation" 
    在开始之前，我们需要把上一章中所有的定义都导入进来：

    From LF Require Export Basics.
    For the Require Export to work, Coq needs to be able to find a compiled version of Basics.v, called Basics.vo, in a directory associated with the prefix LF. This file is analogous to the .class files compiled from .java source files and the .o files compiled from .c files.
    First create a file named _CoqProject containing the following line (if you obtained the whole volume "Logical Foundations" as a single archive, a _CoqProject should already exist and you can skip this step):
    -Q . LF
    This maps the current directory (".", which contains Basics.v, Induction.v, etc.) to the prefix (or "logical directory") "LF". PG and CoqIDE read _CoqProject automatically, so they know to where to look for the file Basics.vo corresponding to the library LF.Basics.
    Once _CoqProject is thus created, there are various ways to build Basics.vo:
    In Proof General: The compilation can be made to happen automatically when you submit the Require line above to PG, by setting the emacs variable coq-compile-before-require to t.
    In CoqIDE: Open Basics.v; then, in the "Compile" menu, click on "Compile Buffer".
    From the command line: Generate a Makefile using the coq_makefile utility, that comes installed with Coq (if you obtained the whole volume as a single archive, a Makefile should already exist and you can skip this step):
    coq_makefile -f _CoqProject *.v -o Makefile
    Note: You should rerun that command whenever you add or remove Coq files to the directory.
    Then you can compile Basics.v by running make with the corresponding .vo file as a target:
    `make Basics.vo`
    All files in the directory can be compiled by giving no arguments:
    `make`
    Under the hood, make uses the Coq compiler, coqc. You can also run coqc directly:
    `coqc -Q . LF Basics.v`
    But make also calculates dependencies between source files to compile them in the right order, so make should generally be prefered over explicit coqc.
    如果你遇到了问题（例如，稍后你可能会在本文件中遇到缺少标识符的提示）， 那可能是因为没有正确设置 Coq 的“加载路径”。指令 Print LoadPath. 能帮你理清这类问题。
    特别是，如果你看到了像这样的信息：
    Compiled library Foo makes inconsistent assumptions over library Bar
    check whether you have multiple installations of Coq on your machine. It may be that commands (like coqc) that you execute in a terminal window are getting a different version of Coq than commands executed by Proof General or CoqIDE.
    Another common reason is that the library Bar was modified and recompiled without also recompiling Foo which depends on it. Recompile Foo, or everything if too many files are affected. (Using the third solution above: make clean; make.)
    再给 CoqIDE 用户一点技巧：如果你看到了 Error: Unable to locate library Basics，那么可能的原因是用 'CoqIDE' 编译的代码和在指令行用 'coqc' 编译的不一致。这通常在系统中安装了两个不兼容的 coqc 时发生 （一个与 CoqIDE 关联，另一个与指令行的 coqc 关联）。这种情况的变通方法 就是只使用 CoqIDE 来编译（即从菜单中选择“make”）并完全避免使用 coqc。
