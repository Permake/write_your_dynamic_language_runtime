package fr.umlv.smalljs.stackinterp;

import static fr.umlv.smalljs.rt.JSObject.UNDEFINED;
import static fr.umlv.smalljs.stackinterp.TagValues.*;

import java.io.PrintStream;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;

import fr.umlv.smalljs.ast.Script;
import fr.umlv.smalljs.rt.Failure;
import fr.umlv.smalljs.rt.JSObject;

public final class StackInterpreter {
    private static void push(int[] stack, int sp, int value) {
        stack[sp] = value;
    }

    private static int pop(int[] stack, int sp) {
        return stack[sp];
    }

    private static int peek(int[] stack, int sp) {
        return stack[sp - 1];
    }

    private static void store(int[] stack, int bp, int offset, int value) {
        stack[bp + offset] = value;
    }

    private static int load(int[] stack, int bp, int offset) {
        return stack[bp + offset];
    }

    private static void dumpStack(String message, int[] stack, int sp, int bp, Dictionary dict, int[] heap) {
        System.err.println(message);
        for (var i = sp - 1; i >= 0; i = i - 1) {
            var value = stack[i];
            try {
                System.err.println(((i == bp) ? "->" : "  ") + value + " " + decodeAnyValue(value, dict, heap));
            } catch (IndexOutOfBoundsException | ClassCastException e) {
                System.err.println(((i == bp) ? "->" : "  ") + value + " (can't decode)");
            }
        }
        System.err.println();
    }

    private static void dumpHeap(String message, int[] heap, int hp, Dictionary dict) {
        System.err.println(message);
        for (var i = 0; i < hp; i++) {
            var value = heap[i];
            try {
                System.err.println(i + ": " + value + " " + decodeAnyValue(value, dict, heap));
            } catch (IndexOutOfBoundsException | ClassCastException e) {
                System.err.println(i + ": " + value + " (can't decode)");
            }
        }
        System.err.println();
    }


    private static final int GC_OFFSET = 1;
    private static final int GC_MARK = -1;
    private static final int GC_EMPTY = -2;

    private static final int BP_OFFSET = 0;
    private static final int PC_OFFSET = 1;
    private static final int FUN_OFFSET = 2;
    private static final int ACTIVATION_SIZE = 3;

    private static final int RECEIVER_BASE_ARG_OFFSET = -1;
    private static final int QUALIFIER_BASE_ARG_OFFSET = -2;
    private static final int FUNCALL_PREFIX = 2;

    public static Object execute(JSObject function, Dictionary dict, JSObject globalEnv) {
        var stack = new int[96 /* 4096 */];
        var heap = new int[96 /* 4096 */];
        var code = (Code) function.lookupOrDefault("__code__", null);
        var instrs = code.instrs();

        var undefined = encodeDictObject(UNDEFINED, dict);

        var hp = 0; // heap pointer
        var pc = 0; // instruction pointer
        var bp = 0; // base pointer
        var sp = bp + code.slotCount() + ACTIVATION_SIZE; // stack pointer

        // initialize all local variables
        for (var i = 0; i < code.slotCount(); i++) {
            stack[i] = undefined;
        }

        for (;;) {
            switch (instrs[pc++]) {
                case Instructions.CONST -> {
                    // get the constant from the instruction to the stack
                    int value = instrs[pc++];
                    push(stack, sp++, value);
                }
                case Instructions.LOOKUP -> {
                    int indexTagValue = instrs[pc++];
                    Object obj = decodeDictObject(indexTagValue, dict);
                    if (!(obj instanceof String name)) {
                        throw new Failure("invalid variable name " + obj);
                    }
                    var value = globalEnv.lookupOrDefault(name, null);
                    if (value == null) {
                        throw new Failure("undefined variable " + name);
                    }
                    push(stack, sp++, encodeAnyValue(value, dict));
                }
                case Instructions.REGISTER -> {
                    // find the current instruction
                    //int indexTagValue = ...
                    // decode the name from the instructions
                    //String name = ...
                    // pop the value from the stack and decode it
                    //Object value = ...
                    // register it in the global environment
                    // globalEnv.register(...);
                    int indexTagValue = instrs[pc++];
                    Object obj = decodeDictObject(indexTagValue, dict);
                    if (!(obj instanceof String name)) {
                        throw new Failure("invalid variable name " + obj);
                    }
                    var value = decodeAnyValue(pop(stack, --sp), dict, heap);
                    globalEnv.register(name, value);
                }
                case Instructions.LOAD -> {
                    // get local offset
                    //int offset = ...
                    // load value from the local slots
                    //int value = ...
                    // push it to the top of the stack
                    //push(...);
                    int offset = instrs[pc++];
                    int value = load(stack, bp, offset);
                    push(stack, sp++, value);
                }
                case Instructions.STORE -> {
                    // get local offset
                    //int offset = ...
                    // pop value from the stack
                    //var value = ...
                    // store it in the local slots
                    //store(...);
                    //dumpStack("in store", stack, sp, bp, dict, heap);
                    int offset = instrs[pc++];
                    int value = pop(stack, --sp);
                    store(stack, bp, offset, value);
                }
                case Instructions.DUP -> {
                    // get value on top of the stack (without remove it)
                    //var value = ...
                    // push it on top of the stack
                    //push(...);
                    //dumpStack("in dup", stack, sp, bp, dict, heap);
                    int value = peek(stack, sp);
                    push(stack, sp++, value);
                    //dumpStack("in dup after", stack, sp, bp, dict, heap);
                }
                case Instructions.POP -> {
                    // adjust the stack pointer
                    --sp;
                }
                case Instructions.SWAP -> {
                    var value1 = pop(stack, --sp);
                    var value2 = pop(stack, --sp);
                    push(stack, sp++, value1);
                    push(stack, sp++, value2);
                }
                case Instructions.FUNCALL -> {
                    var argumentCount = instrs[pc++];
                    var baseArg = sp - argumentCount;
                    var qualifier = decodeAnyValue(stack[baseArg + QUALIFIER_BASE_ARG_OFFSET], dict, heap);
                    if (!(qualifier instanceof JSObject newFunction)) {
                        throw new Failure("can't call non function " + qualifier);
                    }
                    // get the code attribute of the function
                    // check if the function contains a code attribute
                    var maybeCode = newFunction.lookupOrDefault("__code__", null);
                    if (maybeCode == null) { // native call !
                        // decode receiver
                        var receiver = decodeAnyValue(stack[baseArg+RECEIVER_BASE_ARG_OFFSET], dict, heap);
                        var args = new Object[argumentCount];
                        for (var i = 0; i < argumentCount; i++) {
                            args[i] = decodeAnyValue(stack[baseArg + i], dict, heap);
                        }
                        var result = encodeAnyValue(newFunction.invoke(receiver, args), dict);
                        sp = baseArg - FUNCALL_PREFIX;
                        push(stack, sp++, result);
                        continue;
                    }
                    if (!(maybeCode instanceof Code newCode)) {
                        throw new Failure("invalid code attribute in function " + newFunction.name());
                    }
                    // check number of arguments
                    if (newCode.parameterCount() != argumentCount + 1/* this */) {
                        throw new Failure("wrong number of arguments for " + newFunction.name() + " expected "
                                + (newCode.parameterCount() - 1) + " but was " + argumentCount);
                    }

                    // initialize new code
                    code = (Code) maybeCode;

                    // check number of arguments
                    if (code.parameterCount() != argumentCount + 1/* this */) {
                        throw new Failure("wrong number of arguments for " + newFunction.name() + " expected "
                                + (code.parameterCount() - 1) + " but was " + argumentCount);
                    }
                    var activation = baseArg - 1 + code.slotCount();
                    // save bp/pc/code in activation zone
                    stack[activation + BP_OFFSET] = bp;
                    stack[activation + PC_OFFSET] = pc;
                    stack[activation + FUN_OFFSET] = encodeDictObject(function, dict);

                    pc = 0;
                    bp = baseArg - 1;
                    sp = activation + ACTIVATION_SIZE;
                    // copy arguments in local slots
                    for (var i = bp + code.parameterCount(); i< bp; i++) {
                        stack[i] = undefined;
                    }
                    function = newFunction;
                    instrs = code.instrs();

                }
                case Instructions.RET -> {
                    int result = pop(stack, --sp);
                    int activation = bp + code.slotCount();
                    pc = stack[activation + PC_OFFSET];
                    if (pc == 0) {
                        return decodeAnyValue(result, dict, heap);
                    }
                    sp = bp - 1;
                    bp = stack[activation + BP_OFFSET];
                    function = (JSObject) decodeDictObject(stack[activation + FUN_OFFSET], dict);
                    code = (Code) function.lookupOrDefault("__code__", null);
                    instrs = code.instrs();
                    push(stack, sp++, result);
                }
                case Instructions.GOTO -> {
                    pc = instrs[pc];
                }
                case Instructions.JUMP_IF_FALSE -> {
                    var label = instrs[pc++];
                    var condition = pop(stack, --sp);
                    if (condition == TagValues.FALSE) {
                        pc = label;
                    }
                }
                case Instructions.NEW -> {
                    // get the class from the instructions
                    var vClass = instrs[pc++];
                    var clazz = (JSObject) decodeDictObject(vClass, dict);
                    if (hp + OBJECT_HEADER_SIZE + clazz.length() >= heap.length) {
                        dumpHeap("before GC ", heap, hp, dict);
                        throw new UnsupportedOperationException("TODO !!! GC !!!");
                        //dumpHeap("after GC ", heap, hp, dict);
                    }
                    var ref = hp;
                    // write the class on heap
                    heap[ref] = vClass;
                    // write the empty GC mark
                    heap[ref + GC_OFFSET] = GC_EMPTY;
                    // get all fields values from the stack and write them on heap
                    var baseArg = sp - clazz.length();
                    for (var i = 0; i < clazz.length(); i++) {
                        heap[ref + OBJECT_HEADER_SIZE + i] = stack[baseArg + i];
                    }
                    // adjust stack pointer and heap pointer
                    sp = baseArg;
                    hp += OBJECT_HEADER_SIZE + clazz.length();

                    push(stack, sp++, encodeReference(ref));
                }
                case Instructions.GET -> {
                    // get field name from the instructions
                    Object fieldNameObj = decodeDictObject(instrs[pc++], dict);
                    if (!(fieldNameObj instanceof String fieldName)) {
                        throw new Failure("invalid field name " + fieldNameObj);
                    }

                    // get reference from the top of the stack
                    int value = pop(stack, --sp);
                    int ref = decodeReference(value);
                    // get class on heap from the reference
                    int vClass = heap[ref];
                    // get JSObject from class
                    var clazz = (JSObject) decodeDictObject(vClass, dict);
                    // get field slot from JSObject
                    var slot = clazz.lookupOrDefault(fieldName, null);
                    if (slot == null) {
                        // no slot, push undefined
                        push(stack, sp++, undefined);
                        continue;
                    }
                    // get the field index
                    int fieldIndex = (Integer) slot;
                    // get field value
                    int fieldValue = heap[ref + OBJECT_HEADER_SIZE + fieldIndex];
                    // push field value on top of the stack
                    push(stack, sp++, fieldValue);
                }
                case Instructions.PUT -> {
                    // get field name from the instructions
                    var fieldName = (String) decodeDictObject(instrs[pc++], dict);
                    // get new value from the top of the stack
                    var value = pop(stack, --sp);
                    // get reference from the top of the stack
                    var ref = decodeReference(pop(stack, --sp));
                    // get class on heap from the reference
                    var vClass = heap[ref];
                    // get JSObject from class
                    var clazz = (JSObject) decodeDictObject(vClass, dict);
                    // get field slot from JSObject
                    var slot = clazz.lookupOrDefault(fieldName, null);
                    if (slot == null) {
                        throw new Failure("invalid field " + fieldName);
                    }
                    // get the field index
                    var fieldIndex = (Integer) slot;
                    // store field value from the top of the stack on heap
                    heap[ref + OBJECT_HEADER_SIZE + fieldIndex] = value;
                }
                case Instructions.PRINT -> {
                    var result = pop(stack, --sp);
                    var value = decodeAnyValue(result, dict, heap);
                    var print = (JSObject) globalEnv.lookupOrDefault("print", null);
                    //
                    print.invoke(UNDEFINED, new Object[]{value});
                    push(stack, sp++, undefined);
                }
                default -> throw new AssertionError("unknown instruction " + instrs[pc - 1]);
            }
        }
    }


    @SuppressWarnings("unchecked")
    static JSObject createGlobalEnv(PrintStream outStream) {
        var globalEnv = JSObject.newEnv(null);
        globalEnv.register("globalThis", globalEnv);
        globalEnv.register("print", JSObject.newFunction("print", (_, args) -> {
            System.err.println("print called with " + Arrays.toString(args));
            outStream.println(Arrays.stream(args).map(Object::toString).collect(Collectors.joining(" ")));
            return UNDEFINED;
        }));
        globalEnv.register("+", JSObject.newFunction("+", (_, args) -> (Integer) args[0] + (Integer) args[1]));
        globalEnv.register("-", JSObject.newFunction("-", (_, args) -> (Integer) args[0] - (Integer) args[1]));
        globalEnv.register("/", JSObject.newFunction("/", (_, args) -> (Integer) args[0] / (Integer) args[1]));
        globalEnv.register("*", JSObject.newFunction("*", (_, args) -> (Integer) args[0] * (Integer) args[1]));
        globalEnv.register("%", JSObject.newFunction("%", (_, args) -> (Integer) args[0] % (Integer) args[1]));
        globalEnv.register("==", JSObject.newFunction("==", (_, args) -> args[0].equals(args[1]) ? 1 : 0));
        globalEnv.register("!=", JSObject.newFunction("!=", (_, args) -> !args[0].equals(args[1]) ? 1 : 0));
        globalEnv.register("<", JSObject.newFunction("<", (_, args) -> (((Comparable<Object>) args[0]).compareTo(args[1]) < 0) ? 1 : 0));
        globalEnv.register("<=", JSObject.newFunction("<=", (_, args) -> (((Comparable<Object>) args[0]).compareTo(args[1]) <= 0) ? 1 : 0));
        globalEnv.register(">", JSObject.newFunction(">", (_, args) -> (((Comparable<Object>) args[0]).compareTo(args[1]) > 0) ? 1 : 0));
        globalEnv.register(">=", JSObject.newFunction(">=", (_, args) -> (((Comparable<Object>) args[0]).compareTo(args[1]) >= 0) ? 1 : 0));
        return globalEnv;
    }

    public static void interpret(Script script, PrintStream outStream) {
        var globalEnv = createGlobalEnv(outStream);
        var body = script.body();
        var dictionary = new Dictionary();
        var function = InstrRewriter.createFunction("main", List.of(), body, dictionary);
        execute(function, dictionary, globalEnv);
    }
}
