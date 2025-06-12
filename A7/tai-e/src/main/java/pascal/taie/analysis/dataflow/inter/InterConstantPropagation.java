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

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.*;

import static pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation.canHoldInt;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    // 用于存储变量别名关系的映射表
    // key: 变量 x
    // value: 所有与 x 存在别名关系的变量集合 (包含自身)
    private final HashMap<Var, Set<Var>> alias;
    // 存储静态字段加载语句的映射表
    // key: 静态字段 JField 对象
    // value: 所有对该字段执行加载操作的 LoadField 语句集合
    private final HashMap<JField, Set<LoadField>> staticLoadField;
    // 存储静态字段存储语句的映射表
    // key: 静态字段 JField 对象
    // value: 所有对该字段执行存储操作的 StoreField 语句集合
    private final HashMap<JField, Set<StoreField>> staticStoreField;


    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
        // 一些初始化操作
        alias = new HashMap<>();
        staticLoadField = new HashMap<>();
        staticStoreField = new HashMap<>();
    }

    /**
     * 执行初始化操作，主要完成：
     * 1. 构建变量别名关系表
     * 2. 收集静态字段访问语句
     */
    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        // 获取所有变量集合
        Collection<Var> vars = pta.getVars();
        // 第一阶段: 构建变量别名关系
        for (Var x : vars) {
            // 初始化别名集合: 每个变量初始时包含自己
            if (!alias.containsKey(x)) {
                HashSet<Var> set = new HashSet<>();
                set.add(x);
                alias.put(x, set);
            }

            // 检测与其他变量的别名关系
            for (Var y : vars) {
                // 跳过自身比较
                if (x.equals(y)) continue;

                // 别名检测逻辑
                // 当两个变量的 points-to 集合存在交集时:
                // 如果指向相同堆对象, 需要建立别名关系
                boolean hasCommonObj = false;
                for (Obj obj : pta.getPointsToSet(x)) {
                    // 检查是否存在共同指向的对象
                    if (pta.getPointsToSet(y).contains(obj)) {
                        hasCommonObj = true;
                        break;
                    }
                }

                if (hasCommonObj) { // 如果存在共同指向的对象, 则建立别名关系
                    alias.get(x).add(y); // 建立别名关系: y 是 x 的别名
                }
            }
        }
        // 收集静态字段访问语句
        for (Stmt stmt : icfg) { // 遍历整个过程间控制流图
            // 处理静态字段存储语句 (x.f = y)
            if (stmt instanceof StoreField storeField && storeField.isStatic()) {
                JField field = storeField.getFieldRef().resolve();
                // 初始化字段对应的存储语句集合
                if (!staticStoreField.containsKey(field)) {
                    staticStoreField.put(field, new HashSet<>());
                }
                // 记录该字段的存储操作
                staticStoreField.get(field).add(storeField);
            }
            // 处理静态字段加载语句 (y = x.f)
            else if (stmt instanceof LoadField loadField && loadField.isStatic()) {
                JField field = loadField.getFieldRef().resolve();
                // 初始化字段对应的加载语句集合
                if (!staticLoadField.containsKey(field)) {
                    staticLoadField.put(field, new HashSet<>());
                }
                // 记录该字段的加载操作
                staticLoadField.get(field).add(loadField);
            }
        }
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
     * 数组索引一致性检查
     * 判断两个索引值是否相等或至少有一个非常量 (即判断 a[i] 和 b[j] 是否互为别名)
     */
    private boolean checkIndex(Value x, Value y) {
        if (x.isUndef() || y.isUndef()) { // 如果为 UNDEF, 则 x 和 y 不互为别名
            return false;
        }
        if (x.isConstant() && y.isConstant()) { // 如果 x 和 y 都是常量, 则判断是否相等
            return x.equals(y);
        }
        return true;
    }

    /**
     * 非调用节点的数据流传递函数
     * 用于处理不涉及方法调用的语句 (如赋值、字段访问、数组操作等)
     * 核心逻辑:
     *   1. 复制当前 fact
     *   2. 根据语句类型更新 fact
     *   3. 返回 fact 是否发生变化
     */
    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // 1. 复制输入 fact 到输出 fact (默认情况下保持原有值)
        boolean change = false;
        for (Var key : in.keySet()) {
            change |= out.update(key, in.get(key));
        }

        // 2. 处理不同类型的语句
        // 处理字段存储指令 x.f = y
        if (stmt instanceof StoreField storeField) {
            Var r = storeField.getRValue(); // 获取右值变量
            if (canHoldInt(r)) { // 只处理 int 类型变量
                JField field = storeField.getFieldRef().resolve(); // 获取字段引用

                // 静态字段处理
                if (storeField.isStatic()) {
                    // 获取所有对该字段的加载语句
                    Set<LoadField> loadFields = staticLoadField.getOrDefault(field, new HashSet<>());
                    for (Stmt s : loadFields) {
                        solver.add(s); // 添加到工作列表触发分析
                    }
                }
                // 实例字段处理
                else {
                    // 获取字段的基对象 (左侧变量)
                    Var base = ((InstanceFieldAccess) storeField.getLValue()).getBase();
                    // 获取所有与 base 存在别名的变量
                    Set<Var> aliasVars = alias.getOrDefault(base, new HashSet<>());
                    // 收集所有可能影响当前字段的加载指令
                    for (Var x : aliasVars) {
                        for (LoadField loadField : x.getLoadFields()) {
                            // 匹配相同字段 (判断指针集是否有交集)
                            if (loadField.getFieldRef().resolve().equals(field)) {
                                solver.add(loadField);
                            }
                        }
                    }
                }
            }
            change = true; // 字段存储会影响其他语句
        }
        // 处理字段加载指令 y = x.f
        else if (stmt instanceof LoadField loadField) {
            Var l = loadField.getLValue(); // 获取左值变量
            if (canHoldInt(l)) { // 只处理 int 类型
                Value res = Value.getUndef();  // 初始化未定义值
                JField field = loadField.getFieldRef().resolve(); // 获取字段引用

                // 静态字段处理
                if (loadField.isStatic()) {
                    // 获取所有对该字段的存储语句
                    Set<StoreField> storeFields = staticStoreField.getOrDefault(field, new HashSet<>());
                    for (StoreField storeField : storeFields) {
                        CPFact inFact = solver.getInFact(storeField); // 获取输入 fact
                        // 使用 meet 操作合并值 (格理论)
                        res = cp.meetValue(res, inFact.get(storeField.getRValue()));
                    }
                }
                // 实例字段处理
                else {
                    // 获取字段的基对象 (右侧变量)
                    Var base = ((InstanceFieldAccess) loadField.getRValue()).getBase();
                    // 获取所有与 base 存在别名的变量
                    Set<Var> aliasVars = alias.getOrDefault(base, new HashSet<>());
                    // 收集所有可能的存储值
                    for (Var x : aliasVars) {
                        for (StoreField storeField : x.getStoreFields()) {
                            // 匹配相同字段
                            if (storeField.getFieldRef().resolve().equals(field)) {
                                CPFact inFact = solver.getInFact(storeField);
                                // 使用 meet 操作合并值
                                res = cp.meetValue(res, inFact.get(storeField.getRValue()));
                            }
                        }
                    }
                }
                change |= out.update(l, res); // 更新输出 fact
            }
        }
        // 处理数组存储指令 a[i] = x
        else if (stmt instanceof StoreArray storeArray) {
            if (canHoldInt(storeArray.getRValue())) { // 只处理 int 类型
                ArrayAccess ac = storeArray.getArrayAccess(); // 获取数组访问信息
                // 获取数组基变量的别名集合
                Set<Var> aliasVars = alias.getOrDefault(ac.getBase(), new HashSet<>());
                // 收集所有可能影响该数组的加载指令
                for (Var x : aliasVars) {
                    for (LoadArray loadArray : x.getLoadArrays()) {
                        solver.add(loadArray);  // 触发相关分析
                    }
                }
            }
            change = true; // 数组存储会影响其他语句
        }
        // 处理数组加载指令 x = a[i]
        else if (stmt instanceof LoadArray loadArray) {
            Var l = loadArray.getLValue(); // 获取左值变量
            if (canHoldInt(l)) { // 只处理 int 类型
                Value res = Value.getUndef();  // 初始化未定义值
                ArrayAccess ac = loadArray.getArrayAccess(); // 获取数组访问信息
                // 获取数组基变量的别名集合
                Set<Var> aliasVars = alias.getOrDefault(ac.getBase(), new HashSet<>());
                // 收集所有可能的存储值
                for (Var x : aliasVars) {
                    for (StoreArray storeArray : x.getStoreArrays()) {
                        CPFact inFact = solver.getInFact(storeArray); // 获取输入 fact
                        ArrayAccess storeAc = storeArray.getArrayAccess(); // 存储点的数组访问

                        // 检查数组索引是否一致
                        if (checkIndex(
                                in.get(ac.getIndex()), // 当前索引值
                                inFact.get(storeAc.getIndex()) // 存储点索引值
                        )) {
                            // 使用 meet 操作合并值
                            res = cp.meetValue(res, inFact.get(storeArray.getRValue()));
                        }
                    }
                }
                change |= out.update(l, res); // 更新输出 fact
            }
        }
        // 处理普通赋值指令 x = y
        else if (stmt instanceof DefinitionStmt def) {
            LValue l = def.getLValue(); // 获取左值
            if (l instanceof Var x && canHoldInt(x)) { // 判断左值是否为变量并判断 x 是否为 int 类型
                // 计算右值的常量传播结果
                Value res = ConstantPropagation.evaluate(def.getRValue(), in);
                change |= out.update(x, res); // 更新 fact
            }
        }

        return change;
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
        if (def.isPresent() && def.get() instanceof Var lv) {
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
        if (stmt instanceof Invoke invoke) {
            InvokeExp rValue = invoke.getRValue(); // 调用点的右值
            // 遍历被调用方法的实参
            for (int i = 0; i < rValue.getArgCount(); i++) {
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
        if (def.isPresent()) {
            // 初始化返回值变量 (注意应该为 UNDEF 类型)
            Value v = Value.getUndef();
            // 遍历被调用方法的所有可能的返回值, 按照格理论进行合并
            for (Var var : edge.getReturnVars()) v = cp.meetValue(v, returnOut.get(var));
            // 如果调用点左侧有变量, 则更新该变量的值
            if (def.get() instanceof Var lv) fact.update(lv, v);
        }
        return fact;
    }
}