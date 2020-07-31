---
title: Tomcat 学习笔记
category: Teach Yourself
tags: Application
abbrlink: 95ecbeba
date: 2020-07-31 19:48:51
---

https://tomcat.apache.org/

<!-- more -->

## 术语

- **Context** 是指一个 Web 应用

## 目录结构

- `/bin` ：启动、关闭等命令脚本
- `/conf` ：配置文件（和定义文件）
  - `server.xml` 是主配置文件
- `/log` ：log
- `/webapps` ：用户的应用

## `CATLINA_HOME` 和 `CATLINA_BASE`

通常是指向同一个目录的（ Tomcat 的安装目录）。如果需要在一个机器上启动多个 Tomcat 实例，则可以指向不同的目录以获得一些[好处](https://tomcat.apache.org/tomcat-9.0-doc/introduction.html#CATALINA_HOME_and_CATALINA_BASE)。

## 配置

Tomcat 在启动的时候读取所有的配置文件，所以更改配置文件必须重启容器。
