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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.util.collection.SetQueue;

import java.util.ArrayDeque;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    /**
     * ICFG 初始化
     */
    private void initialize() {
        // TODO - finish me
        // 遍历每一个节点, 初始化为空集合 (fact)
        for (Node node : icfg.getNodes()) {
            result.setInFact(node, analysis.newInitialFact());
            result.setOutFact(node, analysis.newInitialFact());
        }
        // 遍历每一个入口方法, 初始化为边界 fact
        for(Method m: icfg.entryMethods().toList()) {
            Node n = icfg.getEntryOf(m);
            result.setInFact(n, analysis.newBoundaryFact(n));
            result.setOutFact(n, analysis.newBoundaryFact(n));
        }
    }

    /**
     * ICFG 过程间常量传播算法实现
     */
    private void doSolve() {
        // TODO - finish me
        workList = new ArrayDeque<>();
        workList.addAll(icfg.getNodes()); // 将所有节点加入工作队列
        while(!workList.isEmpty()) {
            // 处理每一个调用点 node
            Node node = workList.poll();
            // meet 操作, 不过使用传递边来处理方法调用 (相较于过程内常量传播)
            for(ICFGEdge<Node> edge: icfg.getInEdgesOf(node)) {
                analysis.meetInto(analysis.transferEdge(edge, result.getOutFact(edge.getSource())), result.getInFact(node));
            }
            // 如果节点的出边信息发生变化，则将所有后继节点加入工作队列
            if(analysis.transferNode(node, result.getInFact(node), result.getOutFact(node))) {
                workList.addAll(icfg.getSuccsOf(node));
            }
        }
    }

    /**
     * 获取指定节点的输入数据流值 (InFact)
     */
    public Fact getInFact(Node node){
        return result.getInFact(node);
    }

    /**
     * 将指定节点添加到工作队列中, 触发后续的数据流分析
     */
    public void add(Node node){
        this.workList.add(node);
    }
}