# mkdocs 所见所解

## mkdocs.yml --- nav section嵌套
!!! failure "失败的section嵌套"
    nav:

        - section:

            - index.md

            - sub_section:

                - section/sub_section/index.md

                - section/sub_section/part_1.md

                - section/sub_section/part_2.md


!!! success "正确的section嵌套"
    nav:

        - section:

            - index.md

            - sub_section:

                - section/sub_section/index.md

                - part_1: section/sub_section/part_1.md

                - part_2: section/sub_section/part_2.md
                
问题：缺少了part部分的命名。

## 站内跳转链接
推荐用相对路径，路径最后不需要添加文件后缀。
比如`[跳转](./section/sub_section/part_1)`。
