# March 2021

## 02 [无重复字符的最长子窜](https://leetcode-cn.com/problems/longest-substring-without-repeating-characters/)

【初始思路】

1. 从首字符开始增加子串长度，往后每个字符得先看是否在子串中出现过，同时记录当前无重复子串长度CurrentLength以及最长无重复子串长度MaxLength。
2. 出现重复则从首字符的下一字符开始，重复上述过程，直到算出最长无重复子串长度。

【关键优化】

1. 和KMP算法类似，出现重复时，重复字符之前的字符无需再进行步骤一，直接改为从该重复字符之后的字符作为当前无重复子串的首字符，同时对当前无重复子串的长度进行削减。然后继续给子串加字符而没必要再重复多余步骤。
   例子： 
   s = "abcdefgdcba921"
   c = "abcdefg" char = 'd' 出现重复时
   cl = 7, maxl = 7
   令 c = "efgd", cl = cl + 0(a) - 3(d) = 4
   最后 c = "efgdcba921" cl = 10, maxl = 10
2. 当最长无重复子串的长度大于等物当前无重复子串能达到的最大长度时，无需进行计算了，直接输出最大无重复子串长度。举个例子，就很好理解。
   例子：
   s = "abcce"
   c = "abc", char = 'c'
   cl = 3, maxl = 3
   经过第一步优化
   c = "c" , char = 'e'
   cl = 1, maxl = 3, cl(max) = 2 < maxl
   故maxl = 3。

【代码待补】
仔细想了一下思路，但鉴于复习计组可能没时间写代码，日后补上代码。

## 03 [寻找两个正序数组的中位数](https://leetcode-cn.com/problems/median-of-two-sorted-arrays/)

【思路】

1. 被它骗得去合并数组（误，这样指定挺麻烦）
   但其实我自己的思路更麻烦。
2. 叮叮，就是要找中位数嘛，那就去数，因为两个数列本身都是有序的，只要把比中位数小的那些数全部找出来就可以了。举个🌰：
   1，2，4 m = 3
   3，5 n = 2
   m+n=5 5/2=2 这个值可以记为flag
   那就要先找两个小的，显然，1和2，
   具体一点
   1和3比较一下，1更小，m数组下标加一
   2和3比较一下，2更小，m数组下标加一
   此时，已经完成了对中位数之前的数的剔除工作，现在就是要找出中位数了，只需将3和4的进行比较，选择较小项即可。那么中位数就是3。
   \March_2021\3. m和n的和为奇数时，按照上述过程看起来没问题，那么和为偶数的情况下呢？
   举个🌰：
   1，2，4
   3，5，6
   同样经过上述过程的话，
   因为m+n=6，6/2=3，
   最后比较的两个数将会是4和5
   偶数个数找中位数，实际上是中间两个数的平均值，就应该是3和4的平均值，可是最后（数组下标对应）指向的却是4和5。
   逐步分析可以发现，我们剔除了三位数据，而数据3是最后剔除的，但实际上其为有用数据，因此不应该将其剔除，对应的，剔除次数就应该减一，
   即 m+n/2 - 1。
   （小优化，减少重复代码）
   进一步观察发现，m+n为5和6时的剔除次数相同，意味着小奇数和大偶数的剔除次数是相同的，那么，剔除过程完全可以无视奇偶性，即
   剔除次数 flag = (m+n-1)/2。

【存在问题及解决办法】

1. 上述过程忽略了一种特殊情况，即两数组中有一数组过分长了，导致在剔除过程中可能会出现数组越界。

   1. 错误解决办法：忽视较短数组数据，直接将其长度加到长数组中，通过简单方法直接求中位数。想出这种错误方案主要原因是：单纯的认为，长数组的存在一定会导致数据越界，而忽视了短数组内数据的重要性。

   2. 解决办法：当要发生数组越界时（添加循环条件），跳出比较剔除数据循环，改为直接从长数组中找到中位数
      🌰 ：
      1，2 m = 2
      3，4，5，6，7，8，9，10，11，111 n=12

   3. 直接寻找方法（得先判断哪个是长数组）

      flag（原值为6，每剔除一次就减一，为零则表示剔除完了，用作剔除循环的循环条件） 经过两次剔除后变为4。
      长数组此时下标为0
      则下标+4为4，OK，进入计算中位数的时候，和为偶数，长数组下标4和下标5的数据之和的平均值，也就是7和8的平均值7.5。

姑且想了这些，打字打了半天。。。。

【代码待补】

哦，实际还要考虑空数组以及数据相等的情况，得等上手写了代码才知道具体情况如何。

## 04 [正整数拆分](https://blog.csdn.net/Tropine/article/details/104694462)

【待补】

```c
// 同学的代码
#include<stdio.h>
int a[100], n;
void rep(int k, int m, int t){
	for(int i = m; i > 0; i--)
		if(k - i == 0){
			a[t] = i;
            printf("%d=", n);
            for(int j = 0; j < t; j++)
                printf("%d+", a[j]);
            printf("%d\n", a[t]);
	}else if(k - i > 0){
		a[t] = i;
        rep(k - i, i, t + 1);
    }
}
```



## 22 [左旋转字符串](https://leetcode-cn.com/problems/zuo-xuan-zhuan-zi-fu-chuan-lcof/)

【初始思路】

```c++
class Solution {
public:
    string reverseLeftWords(string s, int n) {
        int length = s.length();
        string ans = s;
        for(int i = 0, j = n; i <  length ; i++){
            ans[i] = s[j];
            j = (j + 1) % length;
        }
        return ans;
    }
};
```

【评论区的另类方法】

```c++
class Solution {
public:
    string reverseLeftWords(string s, int n) {
        return s.substr(n,s.length()-n)+(s.substr(0,n));
        // 直接调用string库~ （我觉得题目可能不让我这么做）
    }
};
```

【基于评论区的方法】

```c++
class Solution {
public:
    string reverseLeftWords(string s, int n) {
        return (s+s.substr(0,n)).substr(n,s.length());
    }
};
```



## 29 [颠倒二进制位](https://leetcode-cn.com/problems/reverse-bits/)

左右移位指定不行。
数据声明后要记得初始化！！！
初始化！！

## 30 [搜索二维矩阵](https://leetcode-cn.com/problems/search-a-2d-matrix/)

【思路】

1. 先按行搜索，找到对应行。
2. 再按列一个一个比较。

```c++
class Solution {
public:
    bool searchMatrix(vector<vector<int>>& matrix, int target) {
        int row = 1, col = 0;
        
        for(;row < matrix.size(); row++){
            if( target < matrix[row][0])
                break;
        }
        row--;
        for(;col < matrix[row].size(); col++){
            if(target == matrix[row][col])
                return true;
        }
        return false;
    }
};
```

【错误】

1. 搜索行时行下标row忘记-1。
2. 搜索行时提前判断每行第一个元素是否为target，自以为能够方便后续的列查询操作，使得列查询的col下标初始值为1，导致如果矩阵只有一行，不执行行搜索操作时，将会忽略第一个元素，小细节，大毛病！

【二分搜索的策略】

1. 将二维矩阵的下标一维化，进行二分搜索。
2. 分步对行列进行二分搜索。

```c++
//二分搜索
class Solution {
public:
    bool searchMatrix(vector<vector<int>>& matrix, int target) {
        int col = matrix[0].size();
        int low = 0, high = matrix.size() * col - 1;
        int mid = 0;
        
        while (low <= high){
            mid = (low+high)/2 ;
            if(target == matrix[mid / col][mid % col])
                return true;
            else if (target < matrix[mid / col][mid % col])
                high = mid - 1;
            else
                low = mid + 1;
        }

        return false;
    }
};

// 分步的二分搜索策略
class Solution {
public:
    bool searchMatrix(vector<vector<int>>& matrix, int target) {
        //行列分步，二分搜索 
        int low = 0, high = matrix.size() - 1;
        int mid = 0, row = 0;
        
        while (low <= high){
            mid = (low+high)/2 ;
            if(target == matrix[mid][0])
                return true;
            else if (target < matrix[mid][0])
                high = mid - 1;
            else
                low = mid + 1;
        }
        
        row = (mid == high) ? mid : high;
        if(row < 0)
            return false;
        low = 0;
        high = matrix[0].size() - 1;

        while (low <= high){
            mid = (low+high)/2 ;
            if(target == matrix[row][mid])
                return true;
            else if (target < matrix[row][mid])
                high = mid - 1;
            else
                low = mid + 1;
        }

        return false;
    }
};
```

【问题】

1. 二分搜索的条件是low<=high，不要忘记等号。
2. row_index = mid / col，col_index = mid % col 
3. 分步二分搜索时要进行分类讨论，同时要注意有**row<0**的false情况。

【评论区获得的新知识】

1. 利用矩阵升序的特性从右上角或左下角开始切入。

【类比】

1. 如果是降序情况下呢？
   仍然是从右上角或左下角切入

【总结】**误**

1. 矩阵有序时可以从右上角或左下角开始切入。

【反思】

1. 充分利用**二分法**!
2. 其实从哪个角度切入都是正确的，时间复杂度度都一样，要快还是二分法！

## 31 [子集 II](https://leetcode-cn.com/problems/subsets-ii/)
