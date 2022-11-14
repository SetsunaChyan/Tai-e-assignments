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
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.ArrayList;
import java.util.List;

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
        if (!callGraph.addReachableMethod(method)) return;

        for (Stmt stmt : method.getIR().getStmts()) {
            stmt.accept(stmtProcessor);
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        @Override
        public Void visit(New stmt) {
            // i: x = new T();
            workList.addEntry(pointerFlowGraph.getVarPtr(stmt.getLValue()), new PointsToSet(heapModel.getObj(stmt)));
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Copy stmt) {
            // x = y
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()),
                    pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            // y = T.f
            // we only consider the static load
            JField field = stmt.getFieldRef().resolve();
            if (!field.isStatic()) return null;
            addPFGEdge(pointerFlowGraph.getStaticField(field),
                    pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            // T.f = y
            // we only consider the static store
            JField field = stmt.getFieldRef().resolve();
            if (!field.isStatic()) return null;
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()),
                    pointerFlowGraph.getStaticField(field));
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            // l: r = x.k(a1,…,an)
            // we only consider the static invoke
            if (!stmt.isStatic()) return null;
            JMethod callee = resolveCallee(null, stmt);
            if (callee == null) return null;
            if (callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, callee)))
                addReachable(callee);
            processParamsAndRet(stmt, callee);
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (!pointerFlowGraph.addEdge(source, target)) return;
        if (!source.getPointsToSet().isEmpty())
            workList.addEntry(target, source.getPointsToSet());
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry cur = workList.pollEntry();
            Pointer n = cur.pointer();
            PointsToSet pts = cur.pointsToSet();
            PointsToSet delta = propagate(n, pts);
            for (Obj obj : delta.getObjects()) {
                if (n instanceof VarPtr varPtr) {
                    Var var = varPtr.getVar();
                    for (StoreField storeField : var.getStoreFields()) {
                        if (storeField.isStatic()) continue;
                        JField field = storeField.getFieldRef().resolve();
                        addPFGEdge(pointerFlowGraph.getVarPtr(storeField.getRValue()),
                                pointerFlowGraph.getInstanceField(obj, field));
                    }
                    for (LoadField loadField : var.getLoadFields()) {
                        if (loadField.isStatic()) continue;
                        JField field = loadField.getFieldRef().resolve();
                        addPFGEdge(pointerFlowGraph.getInstanceField(obj, field),
                                pointerFlowGraph.getVarPtr(loadField.getLValue()));
                    }
                    for (StoreArray storeArray : var.getStoreArrays()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(storeArray.getRValue()),
                                pointerFlowGraph.getArrayIndex(obj));
                    }
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        addPFGEdge(pointerFlowGraph.getArrayIndex(obj),
                                pointerFlowGraph.getVarPtr(loadArray.getLValue()));
                    }
                    processCall(var, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet delta = new PointsToSet();
        for (Obj obj : pointsToSet)
            if (!pointer.getPointsToSet().contains(obj)) {
                delta.addObject(obj);
                pointer.getPointsToSet().addObject(obj);
            }
        if (delta.isEmpty()) return delta;
        for (Pointer suc : pointerFlowGraph.getSuccsOf(pointer))
            workList.addEntry(suc, pointsToSet);
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (Invoke invoke : var.getInvokes()) {
            if (invoke.isStatic()) return;
            JMethod m = resolveCallee(recv, invoke);
            workList.addEntry(pointerFlowGraph.getVarPtr(m.getIR().getThis()), new PointsToSet(recv));
            if (callGraph.addEdge(new Edge<>(CallKind.DYNAMIC, invoke, m))) {
                addReachable(m);
                processParamsAndRet(invoke, m);
            }
        }
    }

    private void processParamsAndRet(Invoke invoke, JMethod m) {
        // args
        int argCount = invoke.getRValue().getArgCount();
        for (int i = 0; i < argCount; i++) {
            Var param = m.getIR().getParam(i);
            Var arg = invoke.getRValue().getArg(i);
            addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(param));
        }
        // return var
        Var ret = invoke.getLValue();
        if (ret != null)
            for (Var retVar : m.getIR().getReturnVars())
                addPFGEdge(pointerFlowGraph.getVarPtr(retVar), pointerFlowGraph.getVarPtr(ret));
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
