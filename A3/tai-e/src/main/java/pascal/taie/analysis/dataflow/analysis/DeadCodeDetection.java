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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    /**
     * 死代码检测算法实现
     */
    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // Your task is to recognize dead code in ir and add it to deadCode

        ArrayDeque<Stmt> stmts = new ArrayDeque<>(); // 用于 bfs 的队列, 记录下一条访问的语句 stmt
        Set<Stmt> reached = new HashSet<>(); // 记录已经访问过的语句 stmt
        Set<Stmt> reachable = new HashSet<>(); // 记录可达的语句 stmt
        stmts.add(cfg.getEntry()); // 第一条访问语句为程序入口 Entry
        reachable.add(cfg.getEntry()); // 入口可达
        reachable.add(cfg.getExit()); // 出口可达
        while(!stmts.isEmpty()) { // bfs 遍历
            Stmt stmt = stmts.poll(); // 取队首
            reached.add(stmt); // 标记为已访问
            // 处理 If 语句
            if(stmt instanceof If ifStmt) {
                CPFact fact = constants.getResult(ifStmt); // 获取 ifStmt 的常量传播结果
                ConditionExp cond = ifStmt.getCondition(); // 获取 ifStmt 的条件表达式
                Value value = ConstantPropagation.evaluate(cond, fact); // 获取 ifStmt 的条件表达式的值
                reachable.add(ifStmt); // 标记为可达
                // 如果条件表达式的值是常量, 则根据值判断是否跳转到 true 或 false 分支
                if(value.isConstant()) {
                    // 如果值为 1, 则跳转到 true 分支, 否则跳转到 false 分支
                    if(value.getConstant() == 1) {
                        // 遍历 ifStmt 的所有出边, 如果出边的类型为 IF_TRUE, 则将目标语句加入队列
                        for(Edge<Stmt> edge: cfg.getOutEdgesOf(ifStmt)) {
                            if(edge.getKind() == Edge.Kind.IF_TRUE) {
                                Stmt target = edge.getTarget();
                                // 如果目标语句没有被访问过, 则加入队列
                                if(!reached.contains(target)) {
                                    stmts.add(target);
                                }
                            }
                        }
                    }
                    // 值为 0, 跳转到 false 分支
                    else {
                        // 遍历 ifStmt 的所有出边, 如果出边的类型为 IF_FALSE, 则将目标语句加入队列
                        for(Edge<Stmt> edge: cfg.getOutEdgesOf(ifStmt)) {
                            if(edge.getKind() == Edge.Kind.IF_FALSE) {
                                Stmt target = edge.getTarget();
                                // 如果目标语句没有被访问过, 则加入队列
                                if(!reached.contains(target)) {
                                    stmts.add(target);
                                }
                            }
                        }
                    }
                }
                // 如果条件表达式的值不是常量, 则遍历 ifStmt 的所有出边, 将目标语句加入队列
                else {
                    for(Stmt succ: cfg.getSuccsOf(stmt)) {
                        if(!reached.contains(succ)) {
                            stmts.add(succ);
                        }
                    }
                }
            }
            // 处理 Switch 语句
            else if(stmt instanceof SwitchStmt switchStmt) {
                CPFact fact = constants.getResult(switchStmt); // 获取 switchStmt 的常量传播结果
                Var var = switchStmt.getVar(); // 获取 switchStmt 的变量
                reachable.add(switchStmt); // 标记为可达
                // 如果变量的值是常量, 则根据值判断是否跳转到目标分支
                if(fact.get(var).isConstant()) {
                    int value = fact.get(var).getConstant(); // 获取变量的值
                    boolean isMatched = false; // 标记是否匹配到目标分支
                    // 遍历 switchStmt 的所有出边, 如果出边的类型为 SWITCH_CASE, 则判断值是否匹配, 如果匹配则跳转到目标分支, 否则跳转到默认分支
                    for(Edge<Stmt> edge: cfg.getOutEdgesOf(switchStmt)) {
                        // 如果出边的类型为 SWITCH_CASE，则判断值是否匹配
                        if(edge.getKind() == Edge.Kind.SWITCH_CASE) {
                            // 如果值匹配, 则加入队列
                            if(edge.getCaseValue() == value) {
                                isMatched = true; // 标记匹配到目标分支
                                Stmt target = edge.getTarget();
                                if(!reached.contains(target)) {
                                    stmts.add(target);
                                }
                            }
                        }
                    }
                    // 如果没有匹配到目标分支, 则跳转到默认分支
                    if(!isMatched) {
                        Stmt defaultTarget = switchStmt.getDefaultTarget();
                        if(!reached.contains(defaultTarget)) {
                            stmts.add(defaultTarget);
                        }
                    }
                }
                // 如果变量的值不是常量, 则遍历 switchStmt 的所有出边, 将目标语句加入队列
                else {
                    for(Stmt succ: cfg.getSuccsOf(switchStmt)) {
                        if(!reached.contains(succ)) {
                            stmts.add(succ);
                        }
                    }
                }
            }
            // 处理无用赋值
            else if(stmt instanceof AssignStmt assignStmt) {
                SetFact<Var> live = liveVars.getResult(assignStmt); // 获取 assignStmt 的活跃变量结果
                LValue lValue = assignStmt.getLValue(); // 获取 assignStmt 的左值
                RValue rValue = assignStmt.getRValue(); // 获取 assignStmt 的右值
                boolean flag = true; // 标记是否需要加入可达集合
                // 判断左值是否为 Var 类型, 并且是否不在活跃变量集合中
                if(lValue instanceof Var && !live.contains((Var) lValue)) {
                    // 判断右值是否为无副作用的表达式
                    if(hasNoSideEffect(rValue)) {
                        flag = false;
                    }
                }
                // 如果右值为无副作用的表达式, 并且左值为死变量, 则加入可达集合
                if(flag) {
                    reachable.add(assignStmt);
                }
                // 遍历 assignStmt 的所有出边, 将目标语句加入队列
                for(Stmt succ: cfg.getSuccsOf(assignStmt)) {
                    if(!reached.contains(succ)) {
                        stmts.add(succ);
                    }
                }
            }
            // 其他情况, 均可达
            else {
                reachable.add(stmt);
                for(Stmt succ: cfg.getSuccsOf(stmt)) {
                    if(!reached.contains(succ)) {
                        stmts.add(succ);
                    }
                }
            }
        }
        // 遍历 IR 中的所有语句, 判断是否可达, 如果不可达, 则加入死代码集合
        for(Stmt stmt: ir.getStmts()) {
            if(!reachable.contains(stmt)) {
                deadCode.add(stmt);
            }
        }
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
