---
title: Logical Foundations - Proof by Case Analysis
category: Teach Yourself
tags: Software Foundations
abbrlink: 11fc8540
date: 2020-06-21 22:01:18
---

> https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html#lab37

<!-- more -->

``` coq
Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
```

因为没有给出对`n`的描述，无法得知应当应用加法的哪一条。所以应当针对不同的情况讨论

``` coq
Proof.
  intros n. destruct n as [ | n'] eqn:E.
  - reflexivity.
  - reflexivity.   Qed.
```

- `destruct`用于拆分`n`，得到两个子目标
  - `as [ | n']`：在每一个子目标中引入的变量名
    - 第一个是空的，因为没有构造参数
    - 第二个的构造参数命名为`n'`
  - `eqn:E`：把等式命名为`E`
    - 指的是`n = 0`和`n = S n'`两个等式
    - 如果省略了，那么分情况证明时会忽略这个假设
- bullets `-`：标志证明的不同分支
  - 后面跟的是一个子目标的整个证明
  - 不是必要的，但是有助于可读性

### 逻辑非对合律

``` coq
Theorem negb_involutive : ∀b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.
```

### 逻辑与交换律

``` coq
Theorem andb_commutative : ∀b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.
```

- 除了`-`、`+`还可以用`*`，或者用大括号包起来
- 在大括号内部可以重用其外部已经使用过的bullet

``` coq
Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.
```

### 简写

``` coq
Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
```

### Exercise Solution

``` coq
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - simpl. intros H. rewrite -> H. reflexivity.
  - simpl. destruct c eqn:Ec.
    + intros H. reflexivity.
    + intros H. rewrite -> H. reflexivity.
Qed.
```

