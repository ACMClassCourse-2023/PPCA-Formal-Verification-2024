# Formal-Verification-in-Coq-2024

## 环境配置
推荐在Linux或者WSL环境下开发。

你需要安装8.15.2版本的coq，在已安装 opam (一般都有，若没有请参考[这里](https://github.com/Infinity-Type-Cafe/ntype-cafe-summer-school/blob/main/2023/coq-lean/install.md#linux%E7%94%A8%E6%88%B7%E5%92%8Cwsl%E7%94%A8%E6%88%B7)) 的条件下运行以下指令
```
opam pin add coq 8.15.2
```

推荐在VSCode下安装 **VsCoq Legacy** (注意不是 VsCoq) 后进行开发。

clone 本仓库后在项目根目录执行
```
make depend; make
```
即可编译相关依赖文件。

## 项目安排
我们将先学习 coq 的基本语法和证明技术，再学习如何在 coq 中定义算法和证明算法的正确性，最后自选算法在 coq 中定义和证明其正确性。

coq 基础知识的主要教材是 [Coq定理证明器入门](https://jhc.sjtu.edu.cn/public/courses/CS263/CoqTheoremProver/)，其习题作为平时作业。相关的 ``.v`` 文件在 ``Basic`` 文件夹中。

暂定自选算法是某种**排序算法**(包括quick sort, shell sort等)或者**二叉查找树**。有其他想法请联系助教。

## 参考
- [Software Foundation: Logical Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/index.html)
- [Software Foundation: Verified Functional Algorithms](https://softwarefoundations.cis.upenn.edu/vfa-current/index.html)
