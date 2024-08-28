import os
import argparse

# 定义全局变量
max_depth = 0

def has_md_files(directory):
    """
    判断目录内是否有md文件
    :param directory: 目录路径
    :return: 如果有md文件返回True，否则返回False
    """
    for root, dirs, files in os.walk(directory):
        for file in files:
            if file.endswith('.md'):
                return True
    return False

def get_directory_structure(rootdir, exclude_dirs):
    """
    创建一个嵌套的字典和链表结构来表示目录结构。
    :param rootdir: 根目录路径
    :param exclude_dirs: 要屏蔽的目录列表
    :return: 目录结构的嵌套字典
    """
    global max_depth
    directory_structure = {}

    for dirpath, dirnames, filenames in os.walk(rootdir):
        # 过滤掉要屏蔽的目录
        dirnames[:] = [d for d in dirnames if d not in exclude_dirs]
        dirnames[:] = [d for d in dirnames if has_md_files(os.path.join(dirpath, d))]
        
        # 过滤掉不需要的文件
        filenames[:] = [f for f in filenames if f.endswith('.md')]
        # 为md文件去除后缀
        filenames[:] = [f[:-3] for f in filenames]

        # 获取当前目录的相对路径
        relative_path = os.path.relpath(dirpath, rootdir)
        # 分割路径成各级目录
        parts = relative_path.split(os.sep)

        # 更新最大深度
        current_depth = len(parts)
        if current_depth > max_depth:
            max_depth = current_depth

        # 获取当前目录的字典
        current_level = directory_structure
        for part in parts:
            if part not in current_level:
                current_level[part] = {}
            current_level = current_level[part]
        
        # 添加子目录和文件
        current_level['directories'] = dirnames
        current_level['files'] = filenames

    return directory_structure

def generate_directory_table(directory_structure):
    """
    生成目录结构的多维度列表表示。
    :param directory_structure: 目录结构的嵌套字典
    :return: 多维度列表表示的目录结构
    """
    top = directory_structure['.']
    col_num = max_depth + 1
    table = []
    
    directory_structure['directories'] = top['directories']
    directory_structure['files'] = top['files']
    directory_structure['files'].remove('index')
    
    cur_row = 0
    table.append(['']* col_num)


    # for k, v in directory_structure.items():
    #     print(k + ':', v)

    # directory_structure, level
    def traverse(cur_dir='.', ds=directory_structure, lv=0, path='./'):
        nonlocal cur_row
        
        if cur_dir is None:
            pass
        elif ds['directories']:
            # 根据生成规则，目录不可能为空，必定会有文件或子目录
            # 第一个子目录保持同行，其余子目录加一行

            # !!! note: next_dir 和 cur_dir在同一个ds里面 !!!
            for i, next_dir in enumerate(ds['directories']):
                if i != 0:
                    cur_row += 1
                    table.append(['']* col_num)
                
                # 处理此目录下的的index文件
                if 'index' in ds[next_dir]['files']:
                    table[cur_row][lv] = ('**[' + next_dir + ']('+ os.path.join(path, next_dir) + '/index)/**')
                    ds[next_dir]['files'].remove('index')
                else:
                    table[cur_row][lv] = ('**' + next_dir + '/**')
                
                traverse(next_dir, ds[next_dir], lv+1, path+next_dir+'/')

            # 接下来, 如果此目录下有文件，那就需要额外加一行用来处理文件
            if ds['files']:
                cur_row += 1
                table.append(['']* col_num)

        # 有文件的话，处理文件
        if ds['files']:
            content = ''
            for i, f in enumerate(ds['files']):
                if i != 0:
                    content += '<br><hr>'
                content += '[' + f + '](' + os.path.join(path, f) + ')'
            table[cur_row][lv] = (content)
    
    traverse()
    return table

def print_markdown_table(table=None):
    if table is None:
        return
    
    global max_depth
    # 打印标题和表头
    print('???+ note \"目录\"')
    print('    ', '| 当前 |', end='')
    for i in range(max_depth):
        print('level', (i + 1), '|', end='')
    print()
    print('    ', '|---|', end='')
    for i in range(max_depth):
        print('---|', end='')
    print()

    # 打印表格内容
    for row in table:
        print('    ', '|', end='')
        for col in row:
            print(col, end='|')
        print()

def main():
    parser = argparse.ArgumentParser(description="生成目录结构的嵌套字典表示")
    parser.add_argument("directory", help="要遍历的根目录路径")
    parser.add_argument("--exclude", nargs='*', default=["js", "stylesheets", "Home", "img", "imgs"], 
                        help="要屏蔽的目录列表")
    args = parser.parse_args()

    structure = get_directory_structure(args.directory, args.exclude)
    # print(structure)
    # for k, v in structure.items():
    #     print(k + ':', v)
    # print(max_depth)
    table = generate_directory_table(structure)
    print_markdown_table(table)

if __name__ == "__main__":
    main()