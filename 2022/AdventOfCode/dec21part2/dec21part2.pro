% Copyright

implement dec21part2
    open core

class predicates
    openInput_nd : () -> string nondeterm.
clauses
    openInput_nd() = Line :-
        Dir = directory::getCurrentDirectory(),
        File = string::format("%s/dec21input.txt", Dir),
        Stream = inputStream_file::openFileUtf8(File),
        try
            Stream:repeatToEndOfStream(), %+
                Line = Stream:readLine()
        catch _ do
            Stream:close(),
            fail
        end try.

clauses
    handleFile() :-
        MonkeyMap = mapM_redBlack::new(),
        foreach Line = openInput_nd() and Monkey = parseLine_dt(Line) do
            handleMonkey(MonkeyMap, Monkey)
        end foreach,
        if EQ1 = unpackMonkey(MonkeyMap, "root") and eq(Left, Right) = EQ1 then
            nothing(EQ1),
            if EQ2 = reverseAndApply(Left, Right) then
                nothing(EQ2)
            end if
        end if.

class predicates
    unpackMonkey : (mapM{string Name, monkeyChain}, string Name) -> equation determ.
clauses
    unpackMonkey(MonkeyMap, Name) = EQ :-
        monkeyChain(Monkey, _) = MonkeyMap:tryGet(Name),
        if root(Left, Right) = Monkey then
            LeftEQ = unpackMonkey(MonkeyMap, Left),
            RightEQ = unpackMonkey(MonkeyMap, Right),
            EQ = eq(LeftEQ, RightEQ)
        elseif ops(_, Left, Operation, Right) = Monkey then
            LeftEQ = unpackMonkey(MonkeyMap, Left),
            RightEQ = unpackMonkey(MonkeyMap, Right),
            EQ = operationToEquation(Operation, LeftEQ, RightEQ)
        elseif partialL(_, LeftItem, Operation, Right) = Monkey then
            LeftEQ = n(LeftItem),
            RightEQ = unpackMonkey(MonkeyMap, Right),
            EQ = operationToEquation(Operation, LeftEQ, RightEQ)
        elseif partialR(_, Left, Operation, RightItem) = Monkey then
            LeftEQ = unpackMonkey(MonkeyMap, Left),
            RightEQ = n(RightItem),
            EQ = operationToEquation(Operation, LeftEQ, RightEQ)
        elseif notFound(_) = Monkey then
            EQ = x
        elseif yell(_, Value) = Monkey then
            EQ = n(Value)
        else
            fail
        end if.

class predicates
    reverseAndApply : (equation, equation) -> equation determ.
clauses
    reverseAndApply(x, Equation) = Equation :-
        !.
    reverseAndApply(add(Left, Right), Value) = Equation :-
        %Left + Right = Eq
        (n(Result) = applyEquation(sub(Value, Left)) and Continue = Right orelse n(Result) = applyEquation(sub(Value, Right)) and Continue = Left),
        !,
        Equation = reverseAndApply(Continue, n(Result)).
    reverseAndApply(sub(Left, Right), Value) = Equation :-
        %Left - Right = Eq
        % Left = Eq + Right
        % Right = Left - Eq
        (n(Result) = applyEquation(sub(Left, Value)) and Continue = Right orelse n(Result) = applyEquation(add(Value, Right)) and Continue = Left),
        !,
        Equation = reverseAndApply(Continue, n(Result)).
    reverseAndApply(divide(Left, Right), Value) = Equation :-
        %Left / Right = Eq
        % Left = Eq * Right
        % Right = Left / Eq
        (n(Result) = applyEquation(divide(Left, Value)) and Continue = Right orelse n(Result) = applyEquation(mult(Value, Right)) and Continue = Left),
        !,
        Equation = reverseAndApply(Continue, n(Result)).
    reverseAndApply(mult(Left, Right), Value) = Equation :-
        %Left * Right = Eq
        % Left = Eq / Right
        % Right = Eq / Left
        (n(Result) = applyEquation(divide(Value, Left)) and Continue = Right
            orelse n(Result) = applyEquation(divide(Value, Right)) and Continue = Left),
        !,
        Equation = reverseAndApply(Continue, n(Result)).

class predicates
    applyEquation : (equation) -> equation.
clauses
    applyEquation(add(n(Left), n(Right))) = n(Left + Right) :-
        !.
    applyEquation(sub(n(Left), n(Right))) = n(Left - Right) :-
        !.
    applyEquation(mult(n(Left), n(Right))) = n(Left * Right) :-
        !.
    applyEquation(divide(n(Left), n(Right))) = n(Left div Right) :-
        !.
    applyEquation(Other) = Other.

domains
    equation =
        x;
        n(integer64);
        add(equation, equation);
        sub(equation, equation);
        mult(equation, equation);
        divide(equation, equation);
        eq(equation, equation).

class predicates
    operationToEquation : (operation, equation, equation) -> equation.
clauses
    operationToEquation(add, Left, Right) = add(Left, Right).
    operationToEquation(sub, Left, Right) = sub(Left, Right).
    operationToEquation(mult, Left, Right) = mult(Left, Right).
    operationToEquation(divide, Left, Right) = divide(Left, Right).

class predicates
    handleMonkey : (mapM{string Name, monkeyChain}, monkey).
clauses
    handleMonkey(MonkeyMap, yell(Name, Number)) :-
        !,
        monkeyChain(_NotYelling, WaitingMonkeys) = MonkeyMap:get_default(Name, monkeyChain(notFound(Name), setM_redBlack::new())),
        MonkeyMap:set(Name, monkeyChain(yell(Name, Number), setM_redBlack::new())),
        foreach
            OtherMonkeyName in WaitingMonkeys and OtherMonkeyChain = MonkeyMap:tryGet(OtherMonkeyName)
            and monkeyChain(OtherMonkey, OtherWaitingMonkeys) = OtherMonkeyChain
        do
            if ops(OtherMonkeyName, Name, Operation, Monkey2) = OtherMonkey then
                UpdatedMonkey = partialL(OtherMonkeyName, Number, Operation, Monkey2)
            elseif ops(OtherMonkeyName, Monkey1, Operation, Name) = OtherMonkey then
                UpdatedMonkey = partialR(OtherMonkeyName, Monkey1, Operation, Number)
            elseif partialL(OtherMonkeyName, Value, Operation, Name) = OtherMonkey then
                UpdatedMonkey = yell(OtherMonkeyName, doOperation(Value, Operation, Number))
            elseif partialR(OtherMonkeyName, Name, Operation, Value) = OtherMonkey then
                UpdatedMonkey = yell(OtherMonkeyName, doOperation(Number, Operation, Value))
            else
                UpdatedMonkey = OtherMonkey %Should never happen
            end if,
            handleMonkey(MonkeyMap, UpdatedMonkey)
        end foreach.
    handleMonkey(MonkeyMap, ops(Name, Monkey1, Operation, Monkey2)) :-
        !,
        monkeyChain(Monkey1Obj, WaitingForMonkey1) = MonkeyMap:get_default(Monkey1, monkeyChain(notFound(Monkey1), setM_redBlack::new())),
        if yell(_, Number1) = Monkey1Obj then
            Update1 = partialL(Name, Number1, Operation, Monkey2)
        else
            Update1 = ops(Name, Monkey1, Operation, Monkey2),
            WaitingForMonkey1:insert(Name)
        end if,
        monkeyChain(Monkey2Obj, WaitingForMonkey2) = MonkeyMap:get_default(Monkey2, monkeyChain(notFound(Monkey2), setM_redBlack::new())),
        if yell(_, Number2) = Monkey2Obj then
            if partialL(Name, Value1, Operation, Monkey2) = Update1 then
                Update2 = yell(Name, doOperation(Value1, Operation, Number2))
            else
                Update2 = partialR(Name, Monkey1, Operation, Number2)
            end if
        else
            Update2 = Update1,
            WaitingForMonkey2:insert(Name)
        end if,
        if ops(_, _, _, _) = Update2 then
            monkeyChain(_NotYelling, WaitingMonkeys) = MonkeyMap:get_default(Name, monkeyChain(notFound(Name), setM_redBlack::new())),
            MonkeyMap:set(Name, monkeyChain(ops(Name, Monkey1, Operation, Monkey2), WaitingMonkeys))
        else
            handleMonkey(MonkeyMap, Update2)
        end if.
    handleMonkey(MonkeyMap, root(Monkey1, Monkey2)) :-
        !,
        Name = "root",
        monkeyChain(Monkey1Obj, WaitingForMonkey1) = MonkeyMap:get_default(Monkey1, monkeyChain(notFound(Monkey1), setM_redBlack::new())),
        WaitingForMonkey1:insert(Name),
        monkeyChain(Monkey2Obj, WaitingForMonkey2) = MonkeyMap:get_default(Monkey2, monkeyChain(notFound(Monkey2), setM_redBlack::new())),
        WaitingForMonkey2:insert(Name),
        Monkey = root(Monkey1, Monkey2),
        monkeyChain(_NotYelling, WaitingMonkeys) = MonkeyMap:get_default(Name, monkeyChain(notFound(Name), setM_redBlack::new())),
        MonkeyMap:set(Name, monkeyChain(Monkey, WaitingMonkeys)).
    handleMonkey(MonkeyMap, OtherMonkeyType) :-
        partialL(Name, _, _, _) = OtherMonkeyType,
        !,
        monkeyChain(_NotYelling, WaitingMonkeys) = MonkeyMap:get_default(Name, monkeyChain(notFound(Name), setM_redBlack::new())),
        MonkeyMap:set(Name, monkeyChain(OtherMonkeyType, WaitingMonkeys)).
    handleMonkey(MonkeyMap, OtherMonkeyType) :-
        partialR(Name, _, _, _) = OtherMonkeyType,
        !,
        monkeyChain(_NotYelling, WaitingMonkeys) = MonkeyMap:get_default(Name, monkeyChain(notFound(Name), setM_redBlack::new())),
        MonkeyMap:set(Name, monkeyChain(OtherMonkeyType, WaitingMonkeys)).
    handleMonkey(MonkeyMap, OtherMonkeyType) :-
        notFound(Name) = OtherMonkeyType,
        !,
        monkeyChain(_NotYelling, _WaitingMonkeys) = MonkeyMap:get_default(Name, monkeyChain(notFound(Name), setM_redBlack::new())).
    handleMonkey(_MonkeyMap, _OtherMonkeyType).

class predicates
    doOperation : (integer64, operation, integer64) -> integer64.
clauses
    doOperation(A, add, B) = A + B.
    doOperation(A, sub, B) = A - B.
    doOperation(A, mult, B) = A * B.
    doOperation(A, divide, B) = A div B.

class predicates
    parseLine_dt : (string Line) -> monkey determ.
clauses
    parseLine_dt(Line) = Monkey :-
        Line1 = string::replaceAll(Line, ": ", "\","),
        Result = string::concat("yell(\"", Line1, ")"),
        Monkey0 = tryToTerm(Result),
        !,
        if yell("humn", _) = Monkey0 then
            Monkey = notFound("humn")
        else
            Monkey = Monkey0
        end if.
    parseLine_dt(Line) = Monkey :-
        LineAdd = string::replaceAll(Line, " + ", "\",add,\""),
        LineSub = string::replaceAll(LineAdd, " - ", "\",sub,\""),
        LineMult = string::replaceAll(LineSub, " * ", "\",mult,\""),
        LineDivide = string::replaceAll(LineMult, " / ", "\",divide,\""),
        Line1 = string::replaceAll(LineDivide, ": ", "\",\""),
        Result = string::concat("ops(\"", Line1, "\")"),
        Monkey0 = tryToTerm(Result),
        if ops("root", Monkey1, _, Monkey2) = Monkey0 then
            Monkey = root(Monkey1, Monkey2)
        elseif ops("humn", _, _, _) = Monkey0 then
            Monkey = notFound("humn")
        else
            Monkey = Monkey0
        end if.

domains
    monkeyChain = monkeyChain(monkey, setM{string Names} Waiting).
    monkey =
        ops(string Name, string Monkey1, operation, string Monkey2);
        yell(string Name, integer64);
        notFound(string Name);
        root(string Monkey1, string Monkey2);
        partialL(string Name, integer64, operation, string Monkey2);
        partialR(string Name, string Monkey1, operation, integer64).
    operation = add; sub; mult; divide.

end implement dec21part2
