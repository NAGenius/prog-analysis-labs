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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        // 判断 callGraph 中是否已经存在该方法(其中 RM 已经存在于 callGraph)
        if (!callGraph.contains(csMethod)) { // if c:m ∉ RM
            callGraph.addReachableMethod(csMethod); // add c:𝑚 to RM
            StmtProcessor sp = new StmtProcessor(csMethod); // 与 lab5 不同, 这里需要为每个可达的 CSMethod 创建一个 StmtProcessor 实例
            for (Stmt s : csMethod.getMethod().getIR()) { // 遍历该方法中的所有语句
                s.accept(sp); // 使用访问者模式来处理
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        /**
         * 处理 new 语句: x = new T()
         */
        @Override
        public Void visit(New stmt) {
            Obj obj = heapModel.getObj(stmt); // // 从堆抽象中获取创建点对应的抽象对象
            CSVar csVar = csManager.getCSVar(context, stmt.getLValue()); // 从 CSManager 中获取创建点对应的 CSVar
            Context newContext = contextSelector.selectHeapContext(csMethod, obj); // 获取 new 对象 obj 的上下文
            CSObj csObj = csManager.getCSObj(newContext, obj); // 获取含上下文的对象
            workList.addEntry(csVar, PointsToSetFactory.make(csObj)); // add (c:x, c:o) to WL
            return null;
        }

        /**
         * 处理 Copy 语句: x = y
         */
        @Override
        public Void visit(Copy stmt) {
            CSVar l = csManager.getCSVar(context, stmt.getLValue()); // 获取 Copy 语句的左值(带上下文)
            CSVar r = csManager.getCSVar(context, stmt.getRValue()); // 获取 Copy 语句的右值
            addPFGEdge(r, l); // add (c:y, c:x) to PFG
            return null;
        }

        /**
         * 处理数组 load 语句: x = a[i]
         */
        @Override
        public Void visit(LoadArray stmt) {
            return null; // 和上次一样, 直接返回 null
        }

        /**
         * 处理数组 store 语句: a[i] = y
         */
        @Override
        public Void visit(StoreArray stmt) {
            return null; // 和上次一样, 直接返回 null
        }

        /**
         * 处理 load 语句: y = x.f
         */
        @Override
        public Void visit(LoadField stmt) {
            JField field = stmt.getFieldRef().resolve(); // 获取 LoadField 语句的 load 字段
            if (field.isStatic()) { // 如果是静态字段
                CSVar l = csManager.getCSVar(context, stmt.getLValue()); // 获取左值
                StaticField r = csManager.getStaticField(field); // 获取右值的静态字段
                addPFGEdge(r, l); // add (c:f, c:y) to PFG
            }
            return null;
        }

        /**
         * 处理 store 语句: x.f = y
         */
        @Override
        public Void visit(StoreField stmt) {
            JField field = stmt.getFieldRef().resolve(); // 获取 StoreField 语句的 store 字段
            if (field.isStatic()) { // 如果是静态字段
                CSVar r = csManager.getCSVar(context, stmt.getRValue()); // 获取右值
                StaticField l = csManager.getStaticField(field); // 获取左值的静态字段
                addPFGEdge(r, l); // add (c:y, c:f) to PFG
            }
            return null;
        }

        /**
         * 处理 invoke 语句: x = y.m()
         */
        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) { // 如果是静态方法调用
                JMethod m = resolveCallee(null, stmt); // 解析被调用的方法
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt); // 获取调用点
                Context context1 = contextSelector.selectContext(csCallSite, m); // 获取调用方法 m 的上下文
                CSMethod csMethod = csManager.getCSMethod(context1, m); // 获取带上下文的 CSMethod
                Edge<CSCallSite, CSMethod> edge = new Edge<>(CallKind.STATIC, csCallSite, csMethod); // 创建调用边
                if (callGraph.addEdge(edge)) { // 添加调用边成功
                    addReachable(csMethod); // 添加被调用方法到 RM
                    InvokeExp invokeExp = stmt.getInvokeExp(); // 获取调用表达式
                    // 处理形参和实参
                    for (int i = 0; i < invokeExp.getArgCount(); i++) { // 遍历调用表达式的参数
                        // 注意上下文的不同
                        CSVar argPtr = csManager.getCSVar(context, invokeExp.getArg(i)); // 获取实参的 CSVar
                        CSVar paramPtr = csManager.getCSVar(context1, m.getIR().getParam(i)); // 获取形参的 CSVar
                        addPFGEdge(argPtr, paramPtr); // add (c:a, c:p) to PFG
                    }
                    Var lVar = stmt.getLValue(); // 获取 invoke 语句的左值
                    // 处理返回值
                    if (lVar != null) {
                        CSVar lPtr = csManager.getCSVar(context, lVar); // 获取返回值的 CSVar
                        for (Var ret : m.getIR().getReturnVars()) { // 遍历返回值
                            addPFGEdge(csManager.getCSVar(context1, ret), lPtr); // add (c:r, c:l) to PFG
                        }
                    }
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) { // 如果添加边成功
            if (!source.getPointsToSet().isEmpty()) { // 如果 pt(s) 不为空
                workList.addEntry(target, source.getPointsToSet()); // add (t, pt(s)) to WL
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        // 对应 Solve 中的循环部分
        while (!workList.isEmpty()) { // 如果 WL 不为空
            WorkList.Entry entry = workList.pollEntry(); // 获取 WL 中的第一个元素
            Pointer n = entry.pointer(); // 获取 entry 的指针
            PointsToSet pts = entry.pointsToSet(); // 获取 entry 的 pointsToSet
            PointsToSet delta = propagate(n, pts); // 对 entry 进行传播, 并返回两者的差集
            if (n instanceof CSVar csVar) { // 如果 n 是 CSVar
                Var x = csVar.getVar(); // 获取 Var
                for (CSObj o : delta) { // 遍历 delta 中的对象
                    // 处理实例的 storeFields, x.f = y
                    for (StoreField storeField : x.getStoreFields()) {
                        InstanceField field = csManager.getInstanceField(o, storeField.getFieldRef().resolve()); // 获取实例字段
                        CSVar r = csManager.getCSVar(csVar.getContext(), storeField.getRValue()); // 获取右值
                        addPFGEdge(r, field); // add (c:y, c:f) to PFG
                    }
                    // 处理实例的 loadFields, y = x.f
                    for (LoadField loadField : x.getLoadFields()) {
                        InstanceField field = csManager.getInstanceField(o, loadField.getFieldRef().resolve()); // 获取实例字段
                        CSVar l = csManager.getCSVar(csVar.getContext(), loadField.getLValue()); // 获取左值
                        addPFGEdge(field, l); // add (c:f, c:y) to PFG
                    }
                    // 处理数组的 storeArrays, x[i] = y
                    for (StoreArray storeArray : x.getStoreArrays()) {
                        ArrayIndex index = csManager.getArrayIndex(o); // 获取数组索引
                        CSVar r = csManager.getCSVar(csVar.getContext(), storeArray.getRValue()); // 获取右值
                        addPFGEdge(r, index); // add (c:y, c:i) to PFG
                    }
                    // 处理数组的 loadArrays, y = x[i]
                    for (LoadArray loadArray : x.getLoadArrays()) {
                        ArrayIndex index = csManager.getArrayIndex(o); // 获取数组索引
                        CSVar l = csManager.getCSVar(csVar.getContext(), loadArray.getLValue()); // 获取左值
                        addPFGEdge(index, l); // add (c:i, c:y) to PFG
                    }
                    processCall(csVar, o); // 处理 csVar 调用的实例方法
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
        PointsToSet delta = PointsToSetFactory.make();
        for (CSObj o : pointsToSet) {
            if (!ptn.contains(o)) {
                delta.addObject(o); // 差集
                ptn.addObject(o); // 并集
            }
        }
        if (!delta.isEmpty()) { // 如果 delta 不为空
            for (Pointer s : pointerFlowGraph.getSuccsOf(pointer)) { // 遍历 PFG 中 n 的后继节点(n -> s)
                workList.addEntry(s, pointsToSet); // add (s, pts) to WL
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        // 处理非静态方法的调用
        for (Invoke invoke : recv.getVar().getInvokes()) { // 遍历实例调用
            Context context = recv.getContext(); // 获取 recv 的 context
            JMethod m = resolveCallee(recvObj, invoke); // 获取被调用方法 JMethod
            CSCallSite csCallSite = csManager.getCSCallSite(context, invoke); // 获取调用点
            Context context1 = contextSelector.selectContext(csCallSite, recvObj, m); // 获取调用点的 context
            CSVar m_this = csManager.getCSVar(context1, m.getIR().getThis()); // 获取 m 的 this 指针
            workList.addEntry(m_this, PointsToSetFactory.make(recvObj)); // add (c:this, c:o) to WL
            CSMethod csMethod = csManager.getCSMethod(context1, m); // 获取被调方法 CSMethod
            Edge edge = null;
            // 根据调用类型创建边
            if (invoke.isInterface()) { // 处理接口调用
                edge = new Edge<>(CallKind.INTERFACE, csCallSite, csMethod);
            } else if (invoke.isVirtual()) { // 处理虚调用
                edge = new Edge<>(CallKind.VIRTUAL, csCallSite, csMethod);
            } else if (invoke.isSpecial()) { // 处理特殊调用
                edge = new Edge<>(CallKind.SPECIAL, csCallSite, csMethod);
            } else if (invoke.isDynamic()) { // 处理动态调用
                edge = new Edge<>(CallKind.DYNAMIC, csCallSite, csMethod);
            } else { // 处理其他调用
                edge = new Edge<>(CallKind.OTHER, csCallSite, csMethod);
            }
            // 这一部分和上文处理静态调用方法一致
            if (callGraph.addEdge(edge)) {
                addReachable(csMethod);
                InvokeExp invokeExp = invoke.getInvokeExp();
                // 处理实参和形参
                for (int i = 0; i < invokeExp.getArgCount(); i++) {
                    CSVar argPtr = csManager.getCSVar(context, invokeExp.getArg(i));
                    CSVar paramPtr = csManager.getCSVar(context1, m.getIR().getParam(i));
                    addPFGEdge(argPtr, paramPtr);
                }
                Var lVar = invoke.getLValue();
                // 处理返回值
                if (lVar != null) {
                    CSVar lPtr = csManager.getCSVar(context, lVar);
                    for (Var ret : m.getIR().getReturnVars()) {
                        addPFGEdge(csManager.getCSVar(context1, ret), lPtr);
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
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}