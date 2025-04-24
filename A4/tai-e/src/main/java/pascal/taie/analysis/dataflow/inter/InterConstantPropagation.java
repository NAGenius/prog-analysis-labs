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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.Optional;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    /**
     * 有调用点的传递点处理方法
     */
    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // 因为有调用点, 所有 out = in
        return out.copyFrom(in);
    }

    /**
     * 没有调用点的传递点处理方法
     */
    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // 没有调用点, 所以直接调用 ConstantPropagation 的 transferNode 方法
        return cp.transferNode(stmt, in, out);
    }

    /**
     * Normal Edge 的传递边处理方法
     */
    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        // 普通边, 与过程间调用无关, 前后相等
        return out;
    }

    /**
     * Call-To-Return Edge 的传递边处理方法
     */
    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        // FIXME: 重新创建一份, 不要修改原来的 out (不然有些测试点过不去)
        CPFact copy = out.copy();
        Optional<LValue> def = edge.getSource().getDef(); // 获取调用点的左值
        // 如果调用点左侧(左值)有变量, 则删除 fact 中的该变量
        if(def.isPresent() && def.get() instanceof Var lv) {
            copy.remove(lv);
        }
        return copy;
    }

    /**
     * Call Edge 的传递边处理方法
     */
    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        JMethod callee = edge.getCallee(); // 被调用的方法
        Stmt stmt = edge.getSource(); // 调用点
        CPFact fact = new CPFact();
        if(stmt instanceof Invoke invoke) {
            InvokeExp rValue = invoke.getRValue(); // 调用点的右值
            // 遍历被调用方法的实参
            for(int i = 0; i < rValue.getArgCount(); i++) {
                Var arg = rValue.getArg(i);
                // 更新 fact 相应形参的值 (为对应实参的指)
                fact.update(callee.getIR().getParam(i), callSiteOut.get(arg));
            }
        }
        return fact;
    }

    /**
     * Return Edge 的传递边处理方法
     */
    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact fact = new CPFact();
        Optional<LValue> def = edge.getCallSite().getDef(); // 调用点的左值
        if(def.isPresent()) {
            // 初始化返回值变量 (注意应该为 UNDEF 类型)
            Value v = Value.getUndef();
            // 遍历被调用方法的所有可能的返回值, 按照格理论进行合并
            for(Var var: edge.getReturnVars()) v = cp.meetValue(v, returnOut.get(var));
            // 如果调用点左侧有变量, 则更新该变量的值
            if(def.get() instanceof Var lv) fact.update(lv, v);
        }
        return fact;
    }
}
