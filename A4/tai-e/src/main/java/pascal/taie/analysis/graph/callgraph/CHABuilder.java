/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Stream;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    /**
     * 通过 CHA 进行调用图的构建
     */
    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        // 使用 bfs 遍历
        Queue<JMethod> wl = new ArrayDeque<>(); // bfs 队列
        wl.add(entry); // 程序入口方法入队
        // 进行 bfs
        while(!wl.isEmpty()) {
            JMethod m = wl.poll();
            // 判断方法 m 是否在 callGraph 中 (对应算法中的 rm 可达方法集合)
            // 不新建一个 set 来判断是因为 AbstractCallGraph 已经有一个 reachableMethods
            if(!callGraph.contains(m)) {
                callGraph.addReachableMethod(m);
                Stream<Invoke> invokeStream = callGraph.callSitesIn(m); // 获取调用 site 的所有调用点
                // 遍历调用点, 获取所有调用点对应的方法集合
                for(Invoke cs : invokeStream.toList()) {
                    // 利用 CHA 获取调用点对应的所有方法集合
                    Set<JMethod> T = resolve(cs);
                    for(JMethod m1 : T) {
                        // FIXME: 判断 m1 是否为 null
                        if(m1 == null) continue;
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs), cs, m1)); // 添加边
                        wl.add(m1); // 入队
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> T = new HashSet<>(); // 所有可能的方法集合
        // 获取目标方法引用, 以便获取声明类和子签名
        MethodRef m = callSite.getMethodRef();
        JClass c = m.getDeclaringClass(); // 声明类
        Subsignature s = m.getSubsignature(); // 子签名
        // 根据调用类型, 获取目标方法
        if(callSite.isStatic()) { // 静态方法
            T.add(c.getDeclaredMethod(s));
        }
        if(callSite.isSpecial()){ // 特殊方法
            T.add(dispatch(c, s));
        }
        if(callSite.isVirtual() || callSite.isInterface()) { // 虚方法
            // 通过 bfs 查找所有子类, 子接口, 子实现类, 找到所用目标方法
            Queue<JClass> q = new ArrayDeque<>(); // bfs 队列
            Set<JClass> vis = new HashSet<>(); // 记录访问过的类集合
            // 加入起点类
            q.add(c);
            vis.add(c);
            // 进行 bfs
            while(!q.isEmpty()) {
                JClass subclass = q.poll();
                T.add(dispatch(subclass, s)); // 使用 dispatch 获取目标方法
                // 遍历子类
                for(JClass jc : hierarchy.getDirectSubclassesOf(subclass)) {
                    if(!vis.contains(jc)) {
                        q.add(jc);
                        vis.add(jc);
                    }
                }
                // 遍历子接口
                for(JClass jc : hierarchy.getDirectSubinterfacesOf(subclass)) {
                    if(!vis.contains(jc)) {
                        q.add(jc);
                        vis.add(jc);
                    }
                }
                // 遍历子实现类
                for(JClass jc : hierarchy.getDirectImplementorsOf(subclass)) {
                    if(!vis.contains(jc)) {
                        q.add(jc);
                        vis.add(jc);
                    }
                }
            }
        }
        return T;
    }



    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        // 如果 class 为空, 返回 null
        if(jclass == null) return null;
        JMethod m = jclass.getDeclaredMethod(subsignature); // 根据子签名获取 class 中对应的方法
        // 如果方法 m 不为空, 且方法 m 不是抽象方法, 返回 m
        if(m != null && !m.isAbstract()) return m;
        // 否则, 递归调用 dispatch 方法, 传入 jclass 的父类和子签名 (向上递归)
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
