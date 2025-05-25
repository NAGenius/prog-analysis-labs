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

package pascal.taie.analysis.pta.core.cs.selector;

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.ListContext;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.language.classes.JMethod;

/**
 * Implementation of 2-object sensitivity.
 */
public class _2ObjSelector implements ContextSelector {

    @Override
    public Context getEmptyContext() {
        return ListContext.make();
    }

    /**
     * 为方法调用选择上下文
     */
    @Override
    public Context selectContext(CSCallSite callSite, JMethod callee) {
        // TODO - finish me
        Context context = callSite.getContext(); // 获取调用点的上下文
        int len = context.getLength(); // 获取调用点的上下文长度
        if(len >= 2){
            return ListContext.make(context.getElementAt(len - 2), context.getElementAt(len - 1)); // 获取调用点最近的两个的上下文
        }else if (len == 1){
            return ListContext.make(context.getElementAt(0)); // 获取调用点最近的一个的上下文
        }else{
            return getEmptyContext(); // 返回一个空的上下文
        }
    }

    /**
     * 为实例方法调用选择上下文
     */
    @Override
    public Context selectContext(CSCallSite callSite, CSObj recv, JMethod callee) {
        // TODO - finish me
        Context context = recv.getContext(); // 获取接收者的上下文
        int len = context.getLength(); // 获取接收者的上下文长度
        if(len > 0){
            return ListContext.make(context.getElementAt(len - 1), recv.getObject()); // 获取接收者的最近一个的上下文和接收者对象
        }else{
            return ListContext.make(recv.getObject()); // 返回一个空的上下文和接收者对象
        }
    }

    /**
     * 为堆对象选择上下文
     */
    @Override
    public Context selectHeapContext(CSMethod method, Obj obj) {
        // TODO - finish me
        Context context = method.getContext(); // 获取方法上下文
        int len = context.getLength(); // 获取方法上下文长度
        if(len > 0){
            return ListContext.make(context.getElementAt(len - 1)); // 获取方法最近一个的上下文
        }else{
            return getEmptyContext(); // 返回一个空的上下文
        }
    }
}
