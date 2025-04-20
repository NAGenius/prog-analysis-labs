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

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }

    /**
     * 边界初始化
     */
    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        // 根据返回值, 返回一个 SetFact 实例即可 (不过似乎和 cfg 没什么关系)
        return new SetFact<>();
    }

    /**
     * 非边界基本块初始化
     */
    @Override
    public SetFact<Var> newInitialFact() {
        // TODO - finish me
        // 根据返回值, 返回一个 SetFact 实例即可
        return new SetFact<>();
    }

    /**
     * 处理 SetFact 的合并操作, 对应活跃变量分析中的 OUT = 所有后继 IN 的并集
     */
    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        // TODO - finish me
        // 直接利用 SetFact 已经实现的函数, 进行调用即可
        target.union(fact);
    }

    /**
     * 处理 SetFact 的 IN, OUT 集合的合并操作, 对应活跃变量分析中 IN = USE 并 (OUT - DEF)
     */
    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        // TODO - finish me
        // new 一个新的 SetFact 实例
        SetFact<Var> tmp = new SetFact<>();
        // 相当于直接得到 OUT 集合
        tmp.union(out);
        // 判断是否存在 DEF 集合
        if(stmt.getDef().isPresent()) {
            // 判断 DEF 集合的类型是否为 Var, 在活跃变量分析中, 我们只考虑 Var 类型
            if(stmt.getDef().get() instanceof Var) {
                // 对应 OUT - DEF
                tmp.remove((Var)(stmt.getDef().get()));
            }
        }
        // 遍历 USE 集合
        for(RValue rValue: stmt.getUses()) {
            // 如果是 Var 类型
            if(rValue instanceof Var) {
                // 对应并集操作
                tmp.add((Var)rValue);
            }
        }
        // 判断新得到的 IN 和原来的 IN 是否相同, 如果相同则返回 false, 表示不需要再更新, 否则更新原来的 IN, 返回 true
        if(in.equals(tmp)) {
            return false;
        } else {
            in.set(tmp);
            return true;
        }
    }
}