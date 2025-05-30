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

/**
 * Base class for data-flow analysis solver, which provides common
 * functionalities for different solver implementations.
 *
 * @param <Node> type of CFG nodes
 * @param <Fact> type of data-flow facts
 */
public abstract class Solver<Node, Fact> {

    protected final DataflowAnalysis<Node, Fact> analysis;

    protected Solver(DataflowAnalysis<Node, Fact> analysis) {
        this.analysis = analysis;
    }

    /**
     * Static factory method to create a new solver for given analysis.
     */
    public static <Node, Fact> Solver<Node, Fact> makeSolver(
            DataflowAnalysis<Node, Fact> analysis) {
        return new WorkListSolver<>(analysis);
    }

    /**
     * Starts this solver on the given CFG.
     *
     * @param cfg control-flow graph where the analysis is performed on
     * @return the analysis result
     */
    public DataflowResult<Node, Fact> solve(CFG<Node> cfg) {
        DataflowResult<Node, Fact> result = initialize(cfg);
        doSolve(cfg, result);
        return result;
    }

    /**
     * Creates and initializes a new data-flow result for given CFG.
     *
     * @return the initialized data-flow result
     */
    private DataflowResult<Node, Fact> initialize(CFG<Node> cfg) {
        DataflowResult<Node, Fact> result = new DataflowResult<>();
        if (analysis.isForward()) {
            initializeForward(cfg, result);
        } else {
            initializeBackward(cfg, result);
        }
        return result;
    }

    /**
     * 初始化前向分析
     */
    protected void initializeForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // 初始化 OUT[Entry]
        result.setOutFact(cfg.getEntry(), analysis.newBoundaryFact(cfg));
        // 遍历 cfg 的每一个 node
        for(Node node: cfg) {
            // 如果不是 Entry 节点
            if(!cfg.isEntry(node)) {
                // 初始化 node 的 IN、OUT 集合
                result.setInFact(node, analysis.newInitialFact());
                result.setOutFact(node, analysis.newInitialFact());
            }
        }
    }

    /**
     * 初始化后向分析 (活跃变量分析属于后向分析)
     */
    protected void initializeBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // 为 cfg 的 Exit 节点设置边界集合
        result.setInFact(cfg.getExit(), analysis.newBoundaryFact(cfg));
        // 遍历 cfg 的每一个节点 (迭代求解器)
        for(Node node: cfg) {
            // 如果未到 cfg 的 Exit 节点, 为每个 cfg 的 node 初始化 IN, OUT 集合
            if(!cfg.isExit(node)) {
                result.setInFact(node, analysis.newInitialFact());
                result.setOutFact(node, analysis.newInitialFact());
            }
        }
    }

    /**
     * Solves the data-flow problem for given CFG.
     */
    private void doSolve(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        if (analysis.isForward()) {
            doSolveForward(cfg, result);
        } else {
            doSolveBackward(cfg, result);
        }
    }

    protected abstract void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result);

    protected abstract void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result);
}
