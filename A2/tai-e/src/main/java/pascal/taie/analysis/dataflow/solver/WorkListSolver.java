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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.ArrayList;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    /**
     * 前向分析的实现, 也即是 worklist 求解器用于前向传播算法的具体实现
     */
    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // 初始化一个数组 List
        ArrayList<Node> nodeArrayList = new ArrayList<Node>();
        // 添加所有节点到 List
        for(Node node: cfg) {
            if(!cfg.isEntry(node)) {
                nodeArrayList.add(node);
            }
        }
        // 如果 List 不为空
        while(!nodeArrayList.isEmpty()) {
            // 取出头节点
            Node node = nodeArrayList.remove(0);
            // 对头节点的所有 pred 节点的 OUT 集合做 meet 操作更新 IN 集合
            for(Node pred: cfg.getPredsOf(node)) {
                analysis.meetInto(result.getOutFact(pred), result.getInFact(node));
            }
            // 判断头节点的 OUT 集合是否发生改变
            if(analysis.transferNode(node, result.getInFact(node), result.getOutFact(node))) {
                // 如果发生改变, 则将其后继节点继续加入 List 中, 进行更新
                nodeArrayList.addAll(cfg.getSuccsOf(node));
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}