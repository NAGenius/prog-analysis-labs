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
        if(!callGraph.contains(csMethod)) { // if c:m ∉ RM
            callGraph.addReachableMethod(csMethod); // add c:𝑚 to RM
            StmtProcessor sp = new StmtProcessor(csMethod); // 与 lab5 不同, 这里需要为每个可达的 CSMethod 创建一个 StmtProcessor 实例
            for(Stmt s: csMethod.getMethod().getIR()) { // 遍历该方法中的所有语句
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
        @Override
        public Void visit(New stmt) {
            Obj obj = heapModel.getObj(stmt);
            CSVar csVar = csManager.getCSVar(context, stmt.getLValue());
            Context newContext = contextSelector.selectHeapContext(csMethod, obj);
            CSObj csObj = csManager.getCSObj(newContext, obj);
            workList.addEntry(csVar, PointsToSetFactory.make(csObj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            CSVar l = csManager.getCSVar(context, stmt.getLValue());
            CSVar r = csManager.getCSVar(context, stmt.getRValue());
            addPFGEdge(r, l);
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) {
            return null;
        }

        @Override
        public Void visit(StoreArray stmt) {
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            JField field = stmt.getFieldRef().resolve(); // 获取 LoadField 语句的 load 字段
            if(field.isStatic()) {
                CSVar l = csManager.getCSVar(context, stmt.getLValue());
                StaticField r = csManager.getStaticField(field);
                addPFGEdge(r, l);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            JField field = stmt.getFieldRef().resolve();
            if(field.isStatic()) {
                CSVar r = csManager.getCSVar(context, stmt.getRValue());
                StaticField l = csManager.getStaticField(field);
                addPFGEdge(r, l);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if(stmt.isStatic()) {
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                Var lVar = stmt.getLValue();
                JMethod m = resolveCallee(null, stmt);
                Context context1 = contextSelector.selectContext(csCallSite, m);
                CSMethod csMethod = csManager.getCSMethod(context1, m);
                Edge<CSCallSite, CSMethod> edge = new Edge<>(CallKind.STATIC, csCallSite, csMethod);
                if(callGraph.addEdge(edge)) {
                    addReachable(csMethod);
                    InvokeExp invokeExp = stmt.getInvokeExp();
                    for(int i = 0; i < invokeExp.getArgCount(); i++) {
                        CSVar argPtr = csManager.getCSVar(context, invokeExp.getArg(i));
                        CSVar paramPtr = csManager.getCSVar(context1, m.getIR().getParam(i));
                        addPFGEdge(argPtr, paramPtr);
                    }
                    if(lVar != null) {
                        CSVar lPtr = csManager.getCSVar(context, lVar);
                        for(Var ret: m.getIR().getReturnVars()) {
                            addPFGEdge(csManager.getCSVar(context1, ret), lPtr);
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
        if(pointerFlowGraph.addEdge(source, target)) {
            if(!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer n = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = propagate(n, pts);
            if(n instanceof CSVar csVar) {
                Var x = csVar.getVar();
                for(CSObj o: delta) {
                    for(StoreField storeField: x.getStoreFields()) {
                        InstanceField field = csManager.getInstanceField(o, storeField.getFieldRef().resolve());
                        CSVar r = csManager.getCSVar(csVar.getContext(), storeField.getRValue());
                        addPFGEdge(r, field);
                    }
                    for(LoadField loadField: x.getLoadFields()) {
                        InstanceField field = csManager.getInstanceField(o, loadField.getFieldRef().resolve());
                        CSVar l = csManager.getCSVar(csVar.getContext(), loadField.getLValue());
                        addPFGEdge(field, l);
                    }
                    for(StoreArray storeArray: x.getStoreArrays()) {
                        ArrayIndex index = csManager.getArrayIndex(o);
                        CSVar r = csManager.getCSVar(csVar.getContext(), storeArray.getRValue());
                        addPFGEdge(r, index);
                    }
                    for(LoadArray loadArray: x.getLoadArrays()) {
                        ArrayIndex index = csManager.getArrayIndex(o);
                        CSVar l = csManager.getCSVar(csVar.getContext(), loadArray.getLValue());
                        addPFGEdge(index, l);
                    }
                    processCall(csVar, o);
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
        PointsToSet ptn = pointer.getPointsToSet();
        PointsToSet delta = PointsToSetFactory.make();
        for(CSObj o: pointsToSet) {
            if(!ptn.contains(o)) {
                delta.addObject(o);
                ptn.addObject(o);
            }
        }
        if(!delta.isEmpty()) {
            for(Pointer succ: pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, pointsToSet);
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
        for(Invoke invoke: recv.getVar().getInvokes()) {
            JMethod m = resolveCallee(recvObj, invoke);
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), invoke);
            Context context = recv.getContext();
            Context context1 = contextSelector.selectContext(csCallSite, recvObj, m);
            CSMethod csMethod = csManager.getCSMethod(context, m);
            CSVar m_this = csManager.getCSVar(context, m.getIR().getThis());
            workList.addEntry(m_this, PointsToSetFactory.make(recvObj));
            Edge edge = null;
            // 根据调用类型创建边
            if(invoke.isInterface()) { // 处理接口调用
                edge = new Edge<>(CallKind.INTERFACE, csCallSite, m);
            } else if(invoke.isVirtual()) { // 处理虚调用
                edge = new Edge<>(CallKind.VIRTUAL, csCallSite, m);
            } else if(invoke.isSpecial()) { // 处理特殊调用
                edge = new Edge<>(CallKind.SPECIAL, csCallSite, m);
            } else if(invoke.isDynamic()) { // 处理动态调用
                edge = new Edge<>(CallKind.DYNAMIC, csCallSite, m);
            } else { // 处理其他调用
                edge = new Edge<>(CallKind.OTHER, csCallSite, m);
            }
            if(callGraph.addEdge(edge)) {
                addReachable(csMethod);
                InvokeExp invokeExp = invoke.getInvokeExp();
                for(int i = 0; i < invokeExp.getArgCount(); i++) {
                    CSVar argPtr = csManager.getCSVar(context, invokeExp.getArg(i));
                    CSVar paramPtr = csManager.getCSVar(context1, m.getIR().getParam(i));
                    addPFGEdge(argPtr, paramPtr);
                }
                Var lVar = invoke.getLValue();
                if(lVar != null) {
                    CSVar lPtr = csManager.getCSVar(context, lVar);
                    for(Var ret: m.getIR().getReturnVars()) {
                        addPFGEdge(csManager.getCSVar(context1, ret), lPtr);
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
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
