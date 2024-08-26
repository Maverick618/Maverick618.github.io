import os
from ruamel.yaml import YAML

def generate_nav(base_path, current_path=""):
    nav = []
    items = sorted(os.listdir(os.path.join(base_path, current_path)))
    
    # 确保 index.md 文件排在最前面
    if "index.md" in items:
        items.remove("index.md")
        items.insert(0, "index.md")
    
    for item in items:
        item_path = os.path.join(current_path, item)
        full_path = os.path.join(base_path, item_path)
        if os.path.isdir(full_path):
            sub_nav = generate_nav(base_path, item_path)
            if sub_nav:
                nav.append({item: sub_nav})
        elif item.endswith(".md"):
            if item == "index.md":
                # 使用当前目录名称作为 key
                dir_name = os.path.basename(current_path) if current_path else "首页"
                nav.append({dir_name: item_path.replace("\\", "/")})
            else:
                nav.append({item[:-3]: item_path.replace("\\", "/")})
    return nav
    
def main():
    docs_path = "docs"
    nav = generate_nav(docs_path)
    
    # 读取现有的 mkdocs-test.yml 文件
    yaml = YAML()
    yaml.indent(mapping=4, sequence=4, offset=2)
    yaml.allow_unicode = True
    yaml.default_flow_style = False
    
    try:
        with open("mkdocs.yml", "r", encoding="utf-8") as f:
            mkdocs_config = yaml.load(f)
        
        # 更新 nav 部分
        mkdocs_config["nav"] = nav
        
        # 将更新后的配置写回 mkdocs-test.yml 文件
        with open("mkdocs.yml", "w", encoding="utf-8") as f:
            yaml.dump(mkdocs_config, f)

    except FileNotFoundError:
        print("mkdocs.yml 文件不存在或为空文件！")


if __name__ == "__main__":
    main()