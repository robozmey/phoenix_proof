---- MODULE PhoenixContract ----

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    INITIAL_TIER_ONE_KEY,
    INITIAL_TIER_TWO_KEY,
    BALANCE_LIMIT,
    ADDRESSES,
    MONEY,
    MAX_BLOCK_NUMBER,
    REQUEST_IDS,
    DELAY_CONST

ASSUMPTION BALANCE_LIMIT \in Nat
ASSUMPTION ADDRESSES \subseteq Nat
ASSUMPTION MONEY \subseteq Nat
ASSUMPTION MAX_BLOCK_NUMBER \in Nat
ASSUMPTION REQUEST_IDS \subseteq Nat
ASSUMPTION DELAY_CONST \in Nat
ASSUMPTION INITIAL_TIER_ONE_KEY \in ADDRESSES
ASSUMPTION INITIAL_TIER_TWO_KEY \in ADDRESSES

VARIABLES
    balance,                          \* F
    block_number,                     
    tier_one_addresses,               \* T1
    tier_two_addresses,               \* T2
    delay,                            \* D
    unlock_block,                     \* U
    requests,                         \* R
    previous_command

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
    \* /\ logs \in SUBSET log_type

vars == <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests, previous_command>>

\* log_deposit_type ==
\*     {"deposit"}
\*     \X MONEY    
        
\* log_request_type ==
\*     {"request"}
\*     \X ADDRESSES
\*     \X REQUEST_IDS
\*     \X MONEY  

\* log_withdraw_type ==
\*     {"withdraw"}
\*     \X REQUEST_IDS

\* log_cancel_request_type ==
\*     {"withdraw"}
\*     \X ADDRESSES \X REQUEST_IDS

\* log_cancel_all_requests_type ==
\*     {"withdraw"}
\*     \X tier_one_addresses

\* log_self_request_type ==
\*     {"withdraw"}
\*     \X tier_two_addresses

\* log_lock_type ==
\*     {"withdraw"}
\*     \X ADDRESSES \X (0..MAX_BLOCK_NUMBER)

\* log_add_tier_one_type ==
\*     {"withdraw"}
\*     \X ADDRESSES \X ADDRESSES

\* log_add_tier_two_type ==
\*     {"withdraw"}
\*     \X ADDRESSES \X ADDRESSES

\* log_remove_tier_two_type ==
\*     {"withdraw"}
\*     \X ADDRESSES \X ADDRESSES

\* log_type ==
\*     log_deposit_type
\*     \union log_request_type

Init ==
    /\ balance = 0
    /\ block_number = 0
    /\ tier_one_addresses = {INITIAL_TIER_ONE_KEY}
    /\ tier_two_addresses = {INITIAL_TIER_TWO_KEY}
    /\ delay = DELAY_CONST
    /\ unlock_block = 0
    /\ requests = {}
    /\ previous_command = <<"initial command">>

Tick ==
    /\ block_number + 1 <= MAX_BLOCK_NUMBER
    /\ block_number' = block_number + 1

--------------------------------------
\* Actions

ReduceMapRange(map, op(_,_), ini) ==
    LET dom == DOMAIN map IN 
    LET red[d \in SUBSET dom] ==
        IF d = {} THEN ini 
        ELSE
            LET x == CHOOSE x \in d: TRUE IN 
            op(map[x], red[d \ {x}])
    IN red[dom]

Sum ==
    LET op(req, acc) == req[2] + acc
    IN ReduceMapRange(requests, op, 0)

GetIds == 
    {req[1] : req \in requests}

GetRequestById(id) ==
    CHOOSE req \in {req \in requests: req[1] = id} : TRUE

GetCreationByID(id) ==
    GetRequestById(id)[3]

GetAmountByID(id) ==
    GetRequestById(id)[2]

FilterNotByInitiator(initiator) ==
    {req \in requests: req[4] /= initiator}
                
Deposit(amount) ==
    /\ previous_command' = (<<"deposit", amount>>) 
    /\ amount > 0
    /\ balance + amount <= BALANCE_LIMIT
    /\ balance' = balance + amount
    /\ UNCHANGED <<block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests>>

Request(address2, id, amount) ==
    /\ previous_command' = (<<"request", address2>>) 
    /\ amount > 0
    /\ Sum + amount <= balance
    /\ address2 \in tier_two_addresses
    /\ id \notin GetIds
    /\ requests' = requests \union {<<id, amount, block_number, address2>>}
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block>>

Withdraw(id) == 
    /\ previous_command' = (<<"withdraw", id>>) 
    /\ unlock_block <= block_number
    /\ id \in GetIds
    /\ GetCreationByID(id) + delay <= block_number
    /\ balance' = balance - GetAmountByID(id)
    /\ requests' = requests \ {GetRequestById(id)}
    /\ UNCHANGED <<block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block>>
 
CancelRequest(address1, id) == 
    /\ previous_command' = (<<"cancel_request", address1>>) 
    /\ address1 \in tier_one_addresses
    /\ requests' = requests \ {GetRequestById(id)}
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block>>

CancelAllRequests(address1) ==
    /\ previous_command' =(<<"cancel_all_requests", address1>>) 
    /\ address1 \in tier_one_addresses
    /\ requests' = {}
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block>>

CancelSelfRequest(address2, id) ==
    /\ previous_command' = (<<"cancel_self_request">>) 
    /\ address2 \in tier_two_addresses
    /\ requests' = requests \ {GetRequestById(id)}
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block>>

Lock(address1, new_unlock_block) ==
    /\ previous_command' = (<<"lock", address1>>) 
    /\ address1 \in tier_one_addresses
    /\ new_unlock_block > unlock_block
    /\ new_unlock_block > block_number
    /\ unlock_block' = new_unlock_block
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, requests>>
    
AddTierOneAddress(address1, new_address1) == 
    /\ previous_command' = (<<"add_tier_one", address1>>) 
    /\ address1 \in tier_one_addresses
    /\ new_address1 \notin tier_one_addresses
    /\ new_address1 \notin tier_two_addresses
    /\ tier_one_addresses' = tier_one_addresses \union {new_address1}
    /\ UNCHANGED <<balance, block_number, tier_two_addresses, delay, unlock_block, requests>>

AddTierTwoAddress(address1, new_address2) == 
    /\ previous_command' = (<<"add_tier_two", address1>>) 
    /\ address1 \in tier_one_addresses
    /\ new_address2 \notin tier_one_addresses
    /\ new_address2 \notin tier_two_addresses
    /\ tier_two_addresses' = tier_two_addresses \union {new_address2}
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, delay, unlock_block, requests>>

RemoveTierTwoAddress(address1, remove_address2) == 
    /\ previous_command' = (<<"remove_tier_two", address1>>) 
    /\ address1 \in tier_one_addresses
    /\ remove_address2 \in tier_two_addresses
    /\ tier_two_addresses' = tier_two_addresses \ {remove_address2}
    /\ requests' = FilterNotByInitiator(remove_address2)
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
    \/ \E <<address2, id>> \in tier_two_addresses \X REQUEST_IDS: 
        CancelSelfRequest(address2, id) 
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
\* PROPERTIES

\* 1. Base layer
\* 1.1.
CannotWithdrawBeforeDelay ==
    [][previous_command'[1] = "withdraw" => \A r \in requests: (r[1] = previous_command'[2] => r[3] + delay <= block_number)]_previous_command
\* 1.2.
\* 1.3.
CannotChangeDelay ==
    \E d \in 0..MAX_BLOCK_NUMBER: [](delay = d)

\* 1.4. [](address1 \in tier_one_addresses)
CannotRemoveTierOneAddress == 
    [][\A a \in ADDRESSES: a \in tier_one_addresses => a \in tier_one_addresses']_<<tier_one_addresses>>
    \* \E a \in ADDRESSES: a \in tier_one_addresses
    \* \A a \in ADDRESSES: a \in tier_one_addresses => a \in tier_one_addresses
    \* \A a \in ADDRESSES: <>(a \in tier_one_addresses) => <>[](a \in tier_one_addresses)
    \* \A a \in ADDRESSES: [](a \in tier_one_addresses => a \in tier_one_addresses')
    \* <>(\E address1 \in tier_one_addresses: (address1 \in tier_one_addresses))
\* 1.5.

\* 2. Key separation layer
\* 2.1.
TierOneAndTwoSeparated == 
    [](tier_one_addresses \intersect  tier_two_addresses = {})
\* 2.2
OnlyTierOneCanAddTierOne ==
    [][previous_command'[1] = "add_tier_one" => previous_command'[2] \in tier_one_addresses]_previous_command
\* 2.3


\* 3. Recovery layer
\* 3.1.
MoneyCannotLeaveLocked ==
    \* [][block_number < unlock_block => balance <= balance']_balance
    [][block_number < unlock_block => previous_command'[1] /= "withdraw"]_previous_command
\* 3.2. 
UnlockTimeOnlyIncrease ==
    [][unlock_block <= unlock_block]_block_number
\* 3.3. 
OnlyTierOneCanLock ==
    [][previous_command'[1] = "lock" => previous_command'[2] \in tier_one_addresses]_previous_command
\* 3.4.
OnlyTierOneCanRemoveTierTwo ==
    [][previous_command'[1] = "remove_tier_two" => previous_command'[2] \in tier_one_addresses]_previous_command
\* 3.5.  
OnlyTierOneCanAddTierTwo ==
    [][previous_command'[1] = "add_tier_two" => previous_command'[2] \in tier_one_addresses]_previous_command

\* 4. Tier-one minimization layer
\* 4.1.
BalanceEnoughtToWithdrawAll ==
    [](balance >= Sum)



--------------------------------------

ADDRESSES_const == 0..2
MONEY_const == 0..2
REQUEST_IDS_const == 0..2

====