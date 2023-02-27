# September_2021

#### [678. 有效的括号字符串](https://leetcode-cn.com/problems/valid-parenthesis-string/)

自己的思路是用栈，后来看到这个大佬，属实膜拜。

[【Ryugamine】](https://leetcode-cn.com/problems/valid-parenthesis-string/comments/534393)

对我而言，关键在于**“下限”**的理解和求解。

值得学习

[【官方题解】](https://leetcode-cn.com/problems/valid-parenthesis-string/solution/you-xiao-de-gua-hao-zi-fu-chuan-by-leetc-osi3/)

[【宫水三叶】](https://leetcode-cn.com/problems/valid-parenthesis-string/solution/gong-shui-san-xie-yi-ti-shuang-jie-dong-801rq/)



#### [447. 回旋镖的数量](https://leetcode-cn.com/problems/number-of-boomerangs/)

【以下代码值得学习】

[**【官方题解】**](https://leetcode-cn.com/problems/number-of-boomerangs/solution/hui-xuan-biao-de-shu-liang-by-leetcode-s-lft5/)

```cpp
class Solution {
public:

    int numberOfBoomerangs(vector<vector<int>>& points) {
        int n = points.size();
        if (n < 3) return 0;
        int i, j, x, y,dx,dy;
        vector<vector<int>> dis2(n);

        
        //学习：独特的计算距离方式，计算每个点间的距离
        for (i = 0; i < n; ++i) {
            x = points[i][0];
            y = points[i][1];
            for (j = 0; j < i; ++j) {
                dx = x - points[j][0];
                dy = y - points[j][1];
                dx = dx*dx + dy*dy;
                dis2[i].emplace_back(dx);
                dis2[j].emplace_back(dx);
            }
        }
        
        //类似的排列组合计算，但又有区别
        //i 用作返回值；dis2[i]的大小为n-1，最大秩为n-2,x用来计数
        i = 0;
        y = n - 2;
        for (auto &v : dis2) {
            sort(v.begin(), v.end());
            x = 1;
            for (j = 0; j < y; ++j) {
                if (v[j] != v[j + 1]) { //计算相同距离的点的数量
                    i += (x - 1)*x;
                    x = 1;
                }
                else {
                    ++x;
                }
            }
            i += (x - 1)*x;
        }
        return i;
    }

};
```

#### [524. 通过删除字母匹配到字典里最长单词](https://leetcode-cn.com/problems/longest-word-in-dictionary-through-deleting/)

[【官方题解】](https://leetcode-cn.com/problems/longest-word-in-dictionary-through-deleting/solution/tong-guo-shan-chu-zi-mu-pi-pei-dao-zi-di-at66/) 需要学习：**动态规划**

![image-20210914152059425](D:\Program Code\notes\image-20210914152059425.png)

#### [162. 寻找峰值](https://leetcode-cn.com/problems/find-peak-element/)

[【宫水三叶の相信科学系列】关于能够「二分」的两点证明](https://leetcode-cn.com/problems/find-peak-element/solution/gong-shui-san-xie-noxiang-xin-ke-xue-xi-qva7v/)

值得学习的代码，巧妙利用了整型**数据除法(而且巧用移位运算)向下取整**的特性。

作者的其他学习攻略

**[33. 搜索旋转排序数组](https://mp.weixin.qq.com/s?__biz=MzU4NDE3MTEyMA==&mid=2247485864&idx=1&sn=e5482b2cf55962cd0c5384698d4d0fde&chksm=fd9ca2b7caeb2ba152ef1b900dce805ccfc73cf2a1595fa62eba8a6c5c5212d2d5b3e9f752ba&token=1232059512&lang=zh_CN#rd)** 

```java
class Solution {
    public int findPeakElement(int[] nums) {
        int n = nums.length;
        int l = 0, r = n - 1;
        while (l < r) {
            int mid = l + r >> 1;
            if (nums[mid] > nums[mid + 1]) r = mid;
            else l = mid + 1;
        }
        return r;
    }
}

作者：AC_OIer
链接：https://leetcode-cn.com/problems/find-peak-element/solution/gong-shui-san-xie-noxiang-xin-ke-xue-xi-qva7v/
来源：力扣（LeetCode）
著作权归作者所有。商业转载请联系作者获得授权，非商业转载请注明出处。
```



