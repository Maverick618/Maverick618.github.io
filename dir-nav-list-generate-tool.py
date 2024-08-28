import os
import sys

def generate_nav_table(base_path, current_path="", level=0, exclude_dirs=None):
    nav = []
    items = sorted(os.listdir(os.path.join(base_path, current_path)))
    
    # 确保 index.md 文件排在最前面
    if "index.md" in items:
        items.remove("index.md")
        items.insert(0, "index.md")
    
    has_md_files = False
    for item in items:
        item_path = os.path.join(current_path, item)
        full_path = os.path.join(base_path, item_path)
        
        # 过滤掉不需要的目录
        if exclude_dirs and item in exclude_dirs:
            continue
        
        if os.path.isdir(full_path):
            # 递归处理子目录
            sub_nav = generate_nav_table(base_path, item_path, level + 1, exclude_dirs)
            if sub_nav:
                if "index.md" in os.listdir(full_path):
                    nav.append(f"{'    ' * level}- **[{item}]({item_path.replace('\\', '/')}/index)/**")
                else:
                    nav.append(f"{'    ' * level}- **{item}/**")
                nav.extend(sub_nav)
                has_md_files = True
        elif item.endswith(".md") and item != "index.md":
            # 处理 .md 文件，去除 .md 后缀
            nav.append(f"{'    ' * level}- [{item[:-3]}]({item_path.replace('\\', '/')[:-3]})")
            has_md_files = True
    
    return nav if has_md_files else []

def generate_first_level_nav(base_path, exclude_dirs=None):
    nav = []
    items = sorted(os.listdir(base_path))
    
    # 确保 index.md 文件排在最前面
    if "index.md" in items:
        items.remove("index.md")
        items.insert(0, "index.md")
    
    for item in items:
        item_path = os.path.join(base_path, item)
        
        # 过滤掉不需要的目录
        if exclude_dirs and item in exclude_dirs:
            continue
        
        if os.path.isdir(item_path):
            if "index.md" in os.listdir(item_path):
                nav.append(f"- **[{item}]({item}/index)/**")
            else:
                nav.append(f"- **{item}/**")
        elif item.endswith(".md") and item != "index.md":
            # 处理 .md 文件，去除 .md 后缀
            nav.append(f"- [{item[:-3]}]({item[:-3]})")
    
    return nav

def main():
    if len(sys.argv) < 2:
        print("Usage: python dir-nav-table-generate-tool.py <target_directory> [--L1] [--exclude=<dir1,dir2,...>]")
        sys.exit(1)
    
    target_directory = sys.argv[1]
    first_level_only = False
    exclude_dirs =  ["js", "stylesheets", "Home", "img", "imgs"]
    
    # 解析额外的命令参数
    for arg in sys.argv[2:]:
        if arg == "--L1":
            first_level_only = True
        elif arg.startswith("--exclude="):
            exclude_dirs += arg.split("=")[1].split(",")
    
    if not os.path.isdir(target_directory):
        print(f"Error: {target_directory} is not a valid directory.")
        sys.exit(1)
    
    if first_level_only:
        nav_table = generate_first_level_nav(target_directory, exclude_dirs)
    else:
        nav_table = generate_nav_table(target_directory, exclude_dirs=exclude_dirs)
    
    # 输出 Markdown 格式的导航表
    if nav_table:
        print("# 文件导航\n")
        print("---\n")
        for line in nav_table:
            print(line)
        print("\n---")

if __name__ == "__main__":
    main()