% Copyright

implement dec21part1
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
        if Root = MonkeyMap:tryGet("root") then
            nothing(Root)
        end if.

class predicates
    handleMonkey : (mapM{string Name, monkeyChain}, monkey).
clauses
    handleMonkey(MonkeyMap, yell(Name, Number)) :-
        !,
        monkeyChain(_NotYelling, WaitingMonkeys) = MonkeyMap:get_default(Name, monkeyChain(notFound, setM_redBlack::new())),
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
        monkeyChain(Monkey1Obj, WaitingForMonkey1) = MonkeyMap:get_default(Monkey1, monkeyChain(notFound, setM_redBlack::new())),
        if yell(_, Number1) = Monkey1Obj then
            Update1 = partialL(Name, Number1, Operation, Monkey2)
        else
            Update1 = ops(Name, Monkey1, Operation, Monkey2),
            WaitingForMonkey1:insert(Name)
        end if,
        monkeyChain(Monkey2Obj, WaitingForMonkey2) = MonkeyMap:get_default(Monkey2, monkeyChain(notFound, setM_redBlack::new())),
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
            monkeyChain(_NotYelling, WaitingMonkeys) = MonkeyMap:get_default(Name, monkeyChain(notFound, setM_redBlack::new())),
            MonkeyMap:set(Name, monkeyChain(ops(Name, Monkey1, Operation, Monkey2), WaitingMonkeys))
        else
            handleMonkey(MonkeyMap, Update2)
        end if.
    handleMonkey(MonkeyMap, OtherMonkeyType) :-
        partialL(Name, _, _, _) = OtherMonkeyType,
        !,
        monkeyChain(_NotYelling, WaitingMonkeys) = MonkeyMap:get_default(Name, monkeyChain(notFound, setM_redBlack::new())),
        MonkeyMap:set(Name, monkeyChain(OtherMonkeyType, WaitingMonkeys)).
    handleMonkey(MonkeyMap, OtherMonkeyType) :-
        partialR(Name, _, _, _) = OtherMonkeyType,
        !,
        monkeyChain(_NotYelling, WaitingMonkeys) = MonkeyMap:get_default(Name, monkeyChain(notFound, setM_redBlack::new())),
        MonkeyMap:set(Name, monkeyChain(OtherMonkeyType, WaitingMonkeys)).
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
        Monkey = tryToTerm(Result),
        !.
    parseLine_dt(Line) = Monkey :-
        LineAdd = string::replaceAll(Line, " + ", "\",add,\""),
        LineSub = string::replaceAll(LineAdd, " - ", "\",sub,\""),
        LineMult = string::replaceAll(LineSub, " * ", "\",mult,\""),
        LineDivide = string::replaceAll(LineMult, " / ", "\",divide,\""),
        Line1 = string::replaceAll(LineDivide, ": ", "\",\""),
        Result = string::concat("ops(\"", Line1, "\")"),
        Monkey = tryToTerm(Result).

domains
    monkeyChain = monkeyChain(monkey, setM{string Names} Waiting).
    monkey =
        ops(string Name, string Monkey1, operation, string Monkey2);
        yell(string Name, integer64);
        notFound;
        partialL(string Name, integer64, operation, string Monkey2);
        partialR(string Name, string Monkey1, operation, integer64).
    operation = add; sub; mult; divide.

end implement dec21part1
