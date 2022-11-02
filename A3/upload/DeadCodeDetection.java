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
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import soot.jimple.IfStmt;
import soot.util.Cons;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

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

        Queue<Stmt> q = new LinkedList<>();
        Set<Stmt> vis = new HashSet<>();
        q.offer(cfg.getEntry());

        while (!q.isEmpty()) {
            Stmt cur = q.poll();

            if (vis.contains(cur)) continue;
            vis.add(cur);

            // dead assignment
            if (cur instanceof AssignStmt assignStmt && hasNoSideEffect(assignStmt.getRValue())) {
                if (assignStmt.getLValue() instanceof Var var)
                    if (!liveVars.getOutFact(cur).contains(var)) deadCode.add(cur);
            }

            // reachable
            boolean specialCases = false;
            if (cur instanceof If ifStmt) {
                specialCases = true;
                Value cond = ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getOutFact(cur));
                boolean maybeTrue = !cond.isConstant() || cond.isConstant() && cond.getConstant() == 1;
                boolean maybeFalse = !cond.isConstant() || cond.isConstant() && cond.getConstant() == 0;
                for (Edge e : cfg.getOutEdgesOf(cur)) {
                    if (e.getKind() == Edge.Kind.IF_TRUE && maybeTrue)
                        q.offer((Stmt) e.getTarget());
                    else if (e.getKind() == Edge.Kind.IF_FALSE && maybeFalse)
                        q.offer((Stmt) e.getTarget());
                }
            } else if (cur instanceof SwitchStmt switchStmt) {
                Value cond = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getOutFact(cur));
                if (cond.isConstant()) {
                    specialCases = true;
                    boolean found = false;
                    Stmt defaultTarget = null;
                    for (Edge e : cfg.getOutEdgesOf(cur))
                        if (e.isSwitchCase() && e.getCaseValue() == cond.getConstant()) {
                            found = true;
                            q.offer((Stmt) e.getTarget());
                        } else if(e.getKind() == Edge.Kind.SWITCH_DEFAULT) {
                            defaultTarget = (Stmt) e.getTarget();
                        }
                    if(!found)
                        q.offer(defaultTarget);
                }
            }
            if (!specialCases)
                for (Stmt suc : cfg.getSuccsOf(cur))
                    q.offer(suc);
        }

        for (Stmt stmt : ir)
            if (!vis.contains(stmt)) deadCode.add(stmt);

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