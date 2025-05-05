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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;


class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        // 判断 callGraph 中是否已经存在该方法(其中 RM 已经存在于 callGraph)
        if(!callGraph.contains(method)) { // if m ∉ RM
            callGraph.addReachableMethod(method); // add m to RM
            for(Stmt s: method.getIR().getStmts()) { // 遍历该方法中的所有语句
                s.accept(stmtProcessor); // 使用访问者模式来处理
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        /**
         * 处理 new 语句: x = new T()
         */
        @Override
        public Void visit(New stmt) {
            Obj obj = heapModel.getObj(stmt); // 从堆抽象中获取创建点对应的抽象对象
            VarPtr l = pointerFlowGraph.getVarPtr(stmt.getLValue()); // // 获取左值对应的变量指针
            workList.addEntry(l, new PointsToSet(obj)); // add (x, {o}) to WL, x->o
            return null; // 要求返回值为null
        }

        /**
         * 处理 Copy 语句: x = y
         */
        @Override
        public Void visit(Copy stmt) {
            VarPtr l = pointerFlowGraph.getVarPtr(stmt.getLValue()); // 获取左值对应的变量指针
            VarPtr r = pointerFlowGraph.getVarPtr(stmt.getRValue()); // 获取右值对应的变量指针
            addPFGEdge(r, l); // add (r, l) to PFG
            return null; // 要求返回值为null
        }

        /**
         * 处理数组 load 语句: x = a[i]
         */
        @Override
        public Void visit(LoadArray  stmt) { // 不做处理
            return null; // 要求返回值为null
        }

        /**
         * 处理数组 store 语句: a[i] = y
         */
        @Override
        public Void visit(StoreArray  stmt) { // 不做处理
            return null; // 要求返回值为null
        }

        /**
         * 处理 load 语句: y = x.f
         */
        @Override
        public Void visit(LoadField  stmt) {
            JField field = stmt.getFieldRef().resolve(); // 获取 LoadField 语句的 load 字段
            if(field.isStatic()) { // 如果是静态字段
                VarPtr l = pointerFlowGraph.getVarPtr(stmt.getLValue()); // 获取左值对应的变量指针
                StaticField staticField = pointerFlowGraph.getStaticField(field); // 获取静态字段指针
                addPFGEdge(staticField, l); // 添加边到 PFG
            }
            return null; // 要求返回值为null
        }

        /**
         * 处理 store 语句: x.f = y
         */
        @Override
        public Void visit(StoreField  stmt) {
            JField field = stmt.getFieldRef().resolve(); // 获取 StoreField 语句的 store 字段
            if(field.isStatic()) { // 如果是静态字段
                VarPtr r = pointerFlowGraph.getVarPtr(stmt.getRValue()); // 获取右值对应的变量指针
                StaticField staticField = pointerFlowGraph.getStaticField(field); // 获取静态字段指针
                addPFGEdge(r, staticField); // 添加边到 PFG
            }
            return null; // 要求返回值为null
        }

        /**
         * 处理 invoke 语句: x = y.m()
         */
        @Override
        public Void visit(Invoke  stmt) {
            if(stmt.isStatic()) { // 如果是静态方法调用
                JMethod callee = resolveCallee(null, stmt); // 解析被调用的方法
                Var lVar = stmt.getLValue(); // 获取左值对应的变量
                Edge<Invoke, JMethod> edge = new Edge<>(CallKind.STATIC, stmt, callee); // 创建调用边
                if(callGraph.addEdge(edge)) { // 如果添加成功 (之前没有这条边)
                    addReachable(callee); // 添加被调用方法到 RM
                    InvokeExp invokeExp = stmt.getInvokeExp(); // 获取调用表达式
                    // 处理形参和实参
                    for(int i = 0; i < invokeExp.getArgCount(); i++) { // 遍历调用表达式的参数
                        VarPtr argPtr = pointerFlowGraph.getVarPtr(invokeExp.getArg(i)); // 获取实参的变量指针
                        VarPtr paramPtr = pointerFlowGraph.getVarPtr(callee.getIR().getParam(i)); // 获取形参的变量指针
                        addPFGEdge(argPtr, paramPtr); // 添加边到 PFG
                    }
                    // 处理返回值
                    if(lVar != null) { // 如果有返回值
                        for(Var ret: callee.getIR().getReturnVars()) { // 遍历返回值
                            addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(lVar)); // 添加边到 PFG
                        }
                    }
                }
            }
            return null; // 要求返回值为null
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(pointerFlowGraph.addEdge(source, target)) { // 如果添加成功 (之前没有这条边)
            PointsToSet pt = source.getPointsToSet(); // 获取 source 的 pointsToSet
            if(!pt.isEmpty()) { // 如果 pt(s) 不为空
                workList.addEntry(target, pt); // add (t, pt(s)) to WL
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()) { // 如果 workList 不为空
            WorkList.Entry entry = workList.pollEntry(); // 获取 workList 中的第一个元素
            Pointer ptr = entry.pointer(); // 获取 entry 的指针
            PointsToSet pts = entry.pointsToSet(); // 获取 entry 的 pointsToSet
            PointsToSet delta = propagate(ptr, pts); // 进行传播, 并返回两者的差集

            if(ptr instanceof VarPtr varPtr) { // 如果 ptr 是变量指针
                Var x  = varPtr.getVar(); // 获取 ptr 对应的变量 x
                for(Obj obj: delta) { // 遍历 delta 中的对象
                    // 处理实例的 storeFields, x.f = y
                    for(StoreField storeField: x.getStoreFields()) {
                        JField field = storeField.getFieldRef().resolve(); // 获取 storeField 语句的 store 字段
                        InstanceField  instanceField = pointerFlowGraph.getInstanceField(obj, field); // 获取 obj 对应的实例字段指针
                        VarPtr r = pointerFlowGraph.getVarPtr(storeField.getRValue()); // 获取右值对应的变量指针
                        addPFGEdge(r, instanceField); // 添加边到 PFG
                    }
                    // 处理实例的 loadFields, y = x.f
                    for(LoadField loadField: x.getLoadFields()) {
                        JField field = loadField.getFieldRef().resolve(); // 获取 loadField 语句的 load 字段
                        InstanceField instanceField = pointerFlowGraph.getInstanceField(obj, field); // 获取 obj 对应的实例字段指针
                        VarPtr l = pointerFlowGraph.getVarPtr(loadField.getLValue()); // 获取左值对应的变量指针
                        addPFGEdge(instanceField, l); // 添加边到 PFG
                    }
                    // 处理数组的 storeArrays, x[i] = y
                    for(StoreArray storeArray: x.getStoreArrays()) {
                        ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex(obj); // 获取 obj 对应的数组索引指针
                        VarPtr r = pointerFlowGraph.getVarPtr(storeArray.getRValue()); // 获取右值对应的变量指针
                        addPFGEdge(r, arrayIndex); // 添加边到 PFG
                    }
                    // 处理数组的 loadArrays, y = x[i]
                    for(LoadArray loadArray: x.getLoadArrays()) {
                        ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex(obj); // 获取 obj 对应的数组索引指针
                        VarPtr l = pointerFlowGraph.getVarPtr(loadArray.getLValue()); // 获取左值对应的变量指针
                        addPFGEdge(arrayIndex, l); // 添加边到 PFG
                    }
                    processCall(x, obj); // 处理 x 调用的实例方法
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        // 计算 pts 和 pt(n) 的 delta 差集, 同时更新 pt(n), 对应并集操作
        PointsToSet ptn = pointer.getPointsToSet(); // pt(n)
        PointsToSet delta = new PointsToSet();
        for(Obj obj: pointsToSet) {
            if(!ptn.contains(obj)) {
                delta.addObject(obj); // 差集
                ptn.addObject(obj); // 并集
            }
        }
        //  如果差集不为空
        if(!delta.isEmpty()) {
            // 遍历 pointer 的后继节点
            for(Pointer s: pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(s, pointsToSet); // add (s, pts) to WL
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        // 处理非静态方法的调用
        for(Invoke invoke: var.getInvokes()) { // 遍历实例调用
            JMethod m = resolveCallee(recv, invoke);
            VarPtr m_this = pointerFlowGraph.getVarPtr(m.getIR().getThis()); // 获取 m 的 this 指针
            workList.addEntry(m_this, new PointsToSet(recv)); // add (m_this, {recv}) to WL
            Edge edge = null;
            // 根据调用类型创建边
            if(invoke.isInterface()) { // 处理接口调用
                edge = new Edge<>(CallKind.INTERFACE, invoke, m);
            } else if(invoke.isVirtual()) { // 处理虚调用
                edge = new Edge<>(CallKind.VIRTUAL, invoke, m);
            } else if(invoke.isSpecial()) { // 处理特殊调用
                edge = new Edge<>(CallKind.SPECIAL, invoke, m);
            } else if(invoke.isDynamic()) { // 处理动态调用
                edge = new Edge<>(CallKind.DYNAMIC, invoke, m);
            } else { // 处理其他调用
                edge = new Edge<>(CallKind.OTHER, invoke, m);
            }
            // 这一部分和上文处理静态调用方法一致
            if(callGraph.addEdge(edge)) {
                addReachable(m);
                InvokeExp invokeExp = invoke.getInvokeExp();
                // 处理实参和形参
                for(int i = 0; i < invokeExp.getArgCount(); i++) {
                    VarPtr argPtr = pointerFlowGraph.getVarPtr(invokeExp.getArg(i));
                    VarPtr paramPtr = pointerFlowGraph.getVarPtr(m.getIR().getParam(i));
                    addPFGEdge(argPtr, paramPtr);
                }
                Var lVar = invoke.getLValue();
                // 处理返回值
                if(lVar != null) { // 如果有返回值
                    for(Var ret: m.getIR().getReturnVars()) { // 遍历返回值
                        addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(lVar)); // 添加边到 PFG
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
