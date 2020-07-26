---
title: Coq 02 - 策略
category: Teach Yourself
tags: Coq
abbrlink: fb24fd70
date: 2020-06-21 21:18:19
---

- `intros`
- `simpl`
- `reflexivity`
- `rewrite`
- `destruct`
- `induction`
- `assert`
- `replace`


<!-- more -->

> https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html
> https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html

## Simplification

``` coq
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.  Qed.
```

- `simpl`并不是必要的，`reflexivity`在判断相等时会做一些化简的工作
- `Example`, `Theorem`, `Lemma`, `Fact` and `Remark`是一样的，只是风格不同
- `intros n`把题设中的$\forall n: nat$引入到证明的上下文里来
- `intros`, `simpl`, and `reflexivity`都是预设的策略，用于在`Proof`和`Qed`之间指导证明的运行（类似于指令）

``` coq
Theorem plus_1_l : ∀n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : ∀n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.
```

## Rewriting

### 引入条件并使用

``` coq
Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity.  Qed.
```

- The arrow symbol is pronounced "implies."
- 第二行引入条件 `n = m` 并命名为 `H`.
- 第三行rewrite当前的目标：把当前目标中，`H`的左边替换`H`的右边（即按照从左到右的方向应用`H`到当前的目标上）

### 使用已经证明的定理

``` coq
Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.
```

### 指定rewrite的方式

``` coq
Theorem plus_1_l : forall n: nat, 1 + n = S n.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m H.
  rewrite -> (plus_1_l n).
  rewrite -> H.
  reflexivity.
Qed.
```

## 分情况分析

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

## 数学归纳法


### 右零元

- $n = 0$
- $n = n' \rightarrow n = S n'$

``` coq
Theorem plus_n_O : ∀n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.
```

## 子定理

`assert`: state and prove the needed "sub-theorem" right at the point where it is used.

``` coq
Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.
```

## 代换

`replace` 将表达式中所有的E1替换成E2

``` coq
Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  replace (n + m) with (m + n).
  - rewrite -> plus_assoc. reflexivity.
  - rewrite -> plus_comm. reflexivity.
Qed.
```
