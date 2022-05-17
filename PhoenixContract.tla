---- MODULE PhoenixContract ----

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    BALANCE_LIMIT,
    ADDRESSES,
    MONEY,
    MAX_BLOCK_NUMBER,
    REQUEST_IDS

ASSUMPTION ADDRESSES \subseteq Nat
ASSUMPTION MONEY \subseteq Nat

VARIABLES
    balance,                          \* F
    block_number,                     
    tier_one_addresses,               \* T1
    tier_two_addresses,               \* T2
    delay,                            \* D
    unlock_block,                     \* U
    requests                          \* R

vars == <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests>>

request_type == \* (id, amount, creation, initiator)
    REQUEST_IDS 
    \X MONEY 
    \* \X NETWORK_ADDRESSES 
    \X (0..MAX_BLOCK_NUMBER)
    \X tier_two_addresses

TypeOK ==
    /\ balance \in Nat
    /\ block_number \in 0..MAX_BLOCK_NUMBER
    /\ tier_one_addresses \in SUBSET ADDRESSES
    /\ tier_two_addresses \in SUBSET ADDRESSES
    /\ (tier_one_addresses \intersect tier_two_addresses) = {}
    /\ delay \in 0..MAX_BLOCK_NUMBER
    /\ unlock_block \in 0..MAX_BLOCK_NUMBER
    /\ requests \in SUBSET request_type

Init ==
    /\ balance = 0
    /\ block_number = 0
    /\ tier_one_addresses = {0}
    /\ tier_two_addresses = {}
    /\ delay = 3
    /\ unlock_block = 0
    /\ requests = {}

Tick ==
    /\ block_number + 1 <= MAX_BLOCK_NUMBER
    /\ block_number' = block_number + 1
    /\ UNCHANGED <<balance, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests>>

--------------------------------------
\* Actions

ReduceMapRange(map, op(_,_), ini) ==
    LET dom == DOMAIN  map IN 
    LET red[d \in SUBSET dom] ==
        IF d = {} THEN ini 
        ELSE
            LET x == CHOOSE x \in d: TRUE IN 
            op(map[x], red[d \ {x}])
    IN red[dom]

GetIds == 
    LET red[rs \in SUBSET requests] == 
        IF rs = {} THEN {}
        ELSE 
            LET x == CHOOSE x \in rs: TRUE IN 
            {x[1]} \union red[rs \ {x}]
    IN red[requests]
Deposit(amount) ==
    /\ amount > 0
    /\ balance + amount <= BALANCE_LIMIT
    /\ balance' = balance + amount
    /\ UNCHANGED <<block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests>>

Sum == \* (id, amount, creation, initiator)
    LET red[rs \in SUBSET requests] == 
        IF rs = {} THEN 0
        ELSE 
            LET x == CHOOSE x \in rs: TRUE IN 
                x[2] + red[rs \ {x}]
    IN red[requests]

Request(address2, id, amount) ==
    /\ amount > 0
    /\ Sum + amount <= balance
    /\ address2 \in tier_two_addresses
    /\ id \notin GetIds
    /\ requests' = requests \union {<<id, amount, block_number, address2>>}
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block>>

Count(id) == \* (id, amount, creation, initiator)
    LET red[rs \in SUBSET requests] == 
        IF rs = {} THEN 0
        ELSE 
            LET x == CHOOSE x \in rs: TRUE IN 
                IF x[1] = id THEN 1 + red[rs \ {x}]
                ELSE red[rs \ {x}]
    IN red[requests]

GetCreationByID(id) == \* (id, amount, creation, initiator)
    LET red[rs \in SUBSET requests] == 
        IF rs = {} THEN 0
        ELSE 
            LET x == CHOOSE x \in rs: TRUE IN 
                IF x[1] = id THEN x[3] + red[rs \ {x}]
                ELSE red[rs \ {x}]
    IN red[requests]

GetAmountByID(id) == \* (id, amount, creation, initiator)
    LET red[rs \in SUBSET requests] == 
        IF rs = {} THEN 0
        ELSE 
            LET x == CHOOSE x \in rs: TRUE IN 
                IF x[1] = id THEN x[2] + red[rs \ {x}]
                ELSE red[rs \ {x}]
    IN red[requests]

GetWithoutID(id) == \* (id, amount, creation, initiator)
    LET red[rs \in SUBSET requests] == 
        IF rs = {} THEN {}
        ELSE 
            LET x == CHOOSE x \in rs: TRUE IN 
                IF x[1] = id THEN red[rs \ {x}]
                ELSE {x} \union red[rs \ {x}]
    IN red[requests]   

Withdraw(id) == 
    /\ unlock_block <= block_number
    /\ Count(id) = 1
    /\ GetCreationByID(id) + delay <= block_number
    /\ balance' = balance - GetAmountByID(id)
    /\ requests' = GetWithoutID(id)
    /\ UNCHANGED <<block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block>>
 
CancelRequest(address1, id) == 
    /\ address1 \in tier_one_addresses
    /\ requests' = requests \ GetWithoutID(id)
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block>>

CancelAllRequests(address1) ==
    /\ address1 \in tier_one_addresses
    /\ requests' = {}
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block>>

GetWithoutInitiator(initiator) == \* (id, amount, creation, initiator)
    LET red[rs \in SUBSET requests] == 
        IF rs = {} THEN {}
        ELSE 
            LET x == CHOOSE x \in rs: TRUE IN 
                IF x[4] = initiator THEN red[rs \ {x}]
                ELSE {x} \union red[rs \ {x}]
    IN red[requests]

CancelSelfRequest(address2) ==
    /\ address2 \in tier_two_addresses
    /\ requests' = GetWithoutInitiator(address2)
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block>>

Lock(address1, new_unlock_block) ==
    /\ address1 \in tier_one_addresses
    /\ new_unlock_block > unlock_block
    /\ new_unlock_block > block_number
    /\ unlock_block' = new_unlock_block
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, requests>>
    
AddTierOneAddress(address1, new_address1) == 
    /\ address1 \in tier_one_addresses
    /\ new_address1 \notin tier_one_addresses
    /\ new_address1 \notin tier_two_addresses
    /\ tier_one_addresses' = tier_one_addresses \union {new_address1}
    /\ UNCHANGED <<balance, block_number, tier_two_addresses, delay, unlock_block, requests>>

AddTierTwoAddress(address1, new_address2) == 
    /\ address1 \in tier_one_addresses
    /\ new_address2 \notin tier_one_addresses
    /\ new_address2 \notin tier_two_addresses
    /\ tier_two_addresses' = tier_two_addresses \union {new_address2}
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, delay, unlock_block, requests>>

RemoveTierTwoAddress(address1, remove_address2) == 
    /\ address1 \in tier_one_addresses
    /\ remove_address2 \in tier_two_addresses
    /\ tier_two_addresses' = tier_two_addresses \ {remove_address2}
    /\ requests' = GetWithoutInitiator(remove_address2)
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, delay, unlock_block>>
    

Next ==
    \/ Tick
    \/ \E amount \in MONEY: 
        Deposit(amount)
    \/ \E <<address2, id, amount>> \in ADDRESSES \X REQUEST_IDS \X MONEY:
        Request(address2, id, amount)
    \/ \E id \in REQUEST_IDS: 
        Withdraw(id) 
    \/ \E <<address1, id>> \in ADDRESSES \X REQUEST_IDS: 
        CancelRequest(address1, id)
    \/ \E address1 \in tier_one_addresses: 
        CancelAllRequests(address1) 
    \/ \E address2 \in tier_two_addresses: 
        CancelSelfRequest(address2) 
    \/ \E <<address1, new_unlock_block>> \in ADDRESSES \X (0..MAX_BLOCK_NUMBER): 
        Lock(address1, new_unlock_block)
    \/ \E <<address1, new_address1>> \in ADDRESSES \X ADDRESSES: 
        AddTierOneAddress(address1, new_address1)
    \/ \E <<address1, new_address2>> \in ADDRESSES \X ADDRESSES: 
        AddTierTwoAddress(address1, new_address2)
    \/ \E <<address1, remove_address2>> \in ADDRESSES \X ADDRESSES: 
        RemoveTierTwoAddress(address1, remove_address2)

Spec == Init /\ [][Next]_vars

\* WF = weak fairness

\* liveness

--------------------------------------

ADDRESSES_const == 0..2
MONEY_const == 0..2
REQUEST_IDS_const == 0..2

====