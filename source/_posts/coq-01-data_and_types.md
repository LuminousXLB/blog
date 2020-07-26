---
title: Coq 01 - 数据和类型
category: Teach Yourself
tags: Coq
abbrlink: 1daf1ff0
date: 2020-06-21 13:26:59
---

- `Inductive`
- `Definition`
  - `Compute`
  - `Example` - `Proof`
- `Notation`
- `Check`
- `Module XX` - `End XX`
- `Fixpoint`

<!-- more -->

> https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html

{% note info %}
**CoqIDE的快捷键**

Notice that for all these buttons, except for the *gears* button, their operations are also available in the menu, where their keyboard shortcuts are given.

https://coq.inria.fr/distrib/current/refman/practical-tools/coqide.html#coqintegrateddevelopmentenvironment
{% endnote %}

## 枚举类型(`Inductive`)

``` coq
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.
```

## 函数(`Definition`)

``` coq
Definition next_weekday (d:day) : day :=
  match d with
  | monday ⇒ tuesday
  | tuesday ⇒ wednesday
  | wednesday ⇒ thursday
  | thursday ⇒ friday
  | friday ⇒ monday
  | saturday ⇒ monday
  | sunday ⇒ monday
  end.
```

### `Compute`
   ``` coq
   Compute (next_weekday friday).
   (* ==> monday : day *)
   ```

### `Example` - `Proof`
   ``` coq
   Example test_next_weekday:
     (next_weekday (next_weekday saturday)) = tuesday.
   Proof. simpl. reflexivity. Qed.
   ```
   `Example`做出了一个断言并命名，是一个需要使用Coq命名的目标；`Proof`做出证明。

## 布尔类型

``` coq
Inductive bool : Type :=
  | true
  | false.
```

Coq有内置的布尔类型。

### 逻辑运算

多参数函数的定义。
非、与、或。

``` coq
Definition negb (b:bool) : bool :=
  match b with
  | true ⇒ false
  | false ⇒ true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true ⇒ b2
  | false ⇒ false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true ⇒ true
  | false ⇒ b2
  end.
```

### 运算符(`Notation`)

``` coq
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
```

## 输出表达式的类型(`Check`)

``` coq
Check true.
(* ===> true : bool *)
Check negb.
(* ===> negb : bool -> bool *)
```

## 从已有类型构造新类型

类型的定义中包括一组构造表达式
`primary (p : rgb)`：*the constructor `primary` applied to the argument `p`*

``` coq
Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).
```

给`primary`的参数命名，匹配一个常量，或者使用`_`匹配任意值

``` coq
Definition monochrome (c : color) : bool :=
  match c with
  | black ⇒ true
  | white ⇒ true
  | primary q ⇒ false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black ⇒ false
  | white ⇒ false
  | primary red ⇒ true
  | primary _ ⇒ false
  end.
```

## 元组

### 定义半字节（nybble）

注意`nybble`的定义方式

``` coq
Inductive bit : Type :=
  | B0
  | B1.
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0).
(* ==> bits B1 B0 B1 B0 : nybble *)
```

定义`all_zero`

``` coq
Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) ⇒ true
    | (bits _ _ _ _) ⇒ false
  end.
Compute (all_zero (bits B1 B0 B1 B0)).
(* ===> false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)).
(* ===> true : bool *)
```

## 模块(Module)

If we enclose a collection of declarations between `Module X` and `End X` markers, then, in the remainder of the file after the `End`, these definitions are referred to by names like `X.foo` instead of just `foo`.

类似于命名空间。

``` coq
Module NatPlayground.

(* anything *)

End NatPlayground.
```

## 自然数

### unary number

``` coq
Inductive nat : Type :=
  | O
  | S (n : nat).
```

``` coq
Definition pred (n : nat) : nat :=
  match n with
    | O ⇒ O
    | S n' ⇒ n'
  end.
```

### 算术运算

``` coq
Check (S (S (S (S O)))).
  (* ===> 4 : nat *)
Definition minustwo (n : nat) : nat :=
  match n with
    | O ⇒ O
    | S O ⇒ O
    | S (S n') ⇒ n'
  end.
Compute (minustwo 4).
  (* ===> 2 : nat *)
```

### 判断奇偶(`Fixpoint`)

``` coq
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O ⇒ true
  | S O ⇒ false
  | S (S n') ⇒ evenb n'
  end.
```

``` coq
Definition oddb (n:nat) : bool := negb (evenb n).
```

### 算术运算

``` coq
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O ⇒ m
    | S n' ⇒ S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O ⇒ O
    | S n' ⇒ plus m (mult n' m)
  end.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ ⇒ O
  | S _ , O ⇒ n
  | S n', S m' ⇒ minus n' m'
  end.
End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O ⇒ S O
    | S p ⇒ mult base (exp base p)
  end.
```

## 使用运算符（定义运算符的优先级、运算顺序）

``` coq
Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
```

## 比较（嵌套的match）

``` coq
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O ⇒ match m with
         | O ⇒ true
         | S m' ⇒ false
         end
  | S n' ⇒ match m with
            | O ⇒ false
            | S m' ⇒ eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O ⇒ true
  | S n' ⇒
      match m with
      | O ⇒ false
      | S m' ⇒ leb n' m'
      end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
```
