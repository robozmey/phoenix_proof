---- MODULE PhoenixContract ----

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    INITIAL_TIER_ONE_KEY,
    INITIAL_TIER_TWO_KEY,
    BALANCE_LIMIT,
    OWNER_ADDRESS,
    ADVERSARY_ADDRESS,
    ADDRESSES,
    MONEY,
    MAX_BLOCK_NUMBER,
    REQUEST_IDS,
    DELAY_CONST,
    NETWORK_ADDRESSES,
    SIMULATE_EVENT

ASSUMPTION BALANCE_LIMIT \in Nat
ASSUMPTION ADDRESSES \subseteq Nat
ASSUMPTION MONEY \subseteq Nat
ASSUMPTION MAX_BLOCK_NUMBER \in Nat
ASSUMPTION REQUEST_IDS \subseteq Nat
ASSUMPTION DELAY_CONST \in Nat
ASSUMPTION INITIAL_TIER_ONE_KEY \in ADDRESSES
ASSUMPTION INITIAL_TIER_TWO_KEY \in ADDRESSES
ASSUMPTION OWNER_ADDRESS \in NETWORK_ADDRESSES
ASSUMPTION ADVERSARY_ADDRESS \in NETWORK_ADDRESSES

VARIABLES
    balance,                          \* F
    block_number,                     
    tier_one_addresses,               \* T1
    tier_two_addresses,               \* T2
    delay,                            \* D
    unlock_block,                     \* U
    requests,                         \* R
    previous_command,
    owner_known_addresses,
    adversary_known_addresses

special_vars == <<owner_known_addresses, adversary_known_addresses>>

request_type == \* (id, amount, creation, initiator, recipient)
    REQUEST_IDS 
    \X MONEY 
    \X (0..MAX_BLOCK_NUMBER)
    \X ADDRESSES
    \X NETWORK_ADDRESSES

TypeOK ==
    /\ balance \in [NETWORK_ADDRESSES -> 0..BALANCE_LIMIT]
    /\ block_number \in 0..MAX_BLOCK_NUMBER
    /\ tier_one_addresses \in SUBSET ADDRESSES
    /\ tier_two_addresses \in SUBSET ADDRESSES
    /\ (tier_one_addresses \intersect tier_two_addresses) = {}
    /\ delay \in 0..MAX_BLOCK_NUMBER
    /\ unlock_block \in 0..MAX_BLOCK_NUMBER
    /\ requests \in SUBSET request_type
    /\ owner_known_addresses \in SUBSET ADDRESSES
    /\ adversary_known_addresses \in SUBSET ADDRESSES

vars == <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests, previous_command, special_vars>>

Init ==
    /\ balance = [addr \in NETWORK_ADDRESSES |-> 0]
    /\ block_number = 0
    /\ tier_one_addresses = {INITIAL_TIER_ONE_KEY}
    /\ tier_two_addresses = {INITIAL_TIER_TWO_KEY}
    /\ delay = DELAY_CONST
    /\ unlock_block = 0
    /\ requests = {}
    /\ previous_command = <<"initial command">>
    /\ owner_known_addresses = {INITIAL_TIER_ONE_KEY, INITIAL_TIER_TWO_KEY}
    /\ adversary_known_addresses = {}

Tick ==
    /\ block_number + 1 <= MAX_BLOCK_NUMBER
    /\ block_number' = block_number + 1

--------------------------------------
\* Actions

Sum == \* (id, amount, creation, initiator)
    LET red[rs \in SUBSET requests] == 
        IF rs = {} THEN 0
        ELSE 
            LET x == CHOOSE x \in rs: TRUE IN 
                x[2] + red[rs \ {x}]
    IN red[requests]

GetIds == 
    {req[1] : req \in requests}

GetRequestById(id) ==
    CHOOSE req \in {req \in requests: req[1] = id} : TRUE

GetCreationByID(id) ==
    GetRequestById(id)[3]

GetAmountByID(id) ==
    GetRequestById(id)[2]

GetAddressByID(id) ==
    GetRequestById(id)[5]

FilterNotByInitiator(initiator) ==
    {req \in requests: req[4] /= initiator}
                
Deposit(amount) ==
    /\ Tick
    /\ previous_command' = (<<"deposit", amount>>) 
    /\ amount > 0
    /\ balance[OWNER_ADDRESS] + amount <= BALANCE_LIMIT
    /\ balance' = [balance EXCEPT ![OWNER_ADDRESS] = @ + amount]
    /\ UNCHANGED <<tier_one_addresses, tier_two_addresses, delay, unlock_block, requests, special_vars>>

Request(address2, amount, recipient) ==
    /\ Tick
    /\ recipient /= OWNER_ADDRESS
    /\ recipient /= 0
    /\ previous_command' = (<<"request", address2>>) 
    /\ amount > 0
    /\ Sum + amount <= balance[OWNER_ADDRESS]
    /\ balance[recipient] + amount <= BALANCE_LIMIT
    /\ address2 \in tier_two_addresses
    /\ requests' = requests \union {<<block_number, amount, block_number, address2, recipient>>}
    /\ UNCHANGED <<balance, tier_one_addresses, tier_two_addresses, delay, unlock_block, special_vars>>

Withdraw(id) == 
    /\ Tick
    /\ previous_command' = (<<"withdraw", id>>) 
    /\ unlock_block <= block_number
    /\ id \in GetIds
    /\ GetAddressByID(id) /= OWNER_ADDRESS
    /\ GetCreationByID(id) + delay <= block_number
    /\ LET balance1 == [balance EXCEPT ![OWNER_ADDRESS] = @ - GetAmountByID(id)]
       IN balance' = [balance1 EXCEPT ![GetAddressByID(id)] = @ + GetAmountByID(id)]
    /\ requests' = requests \ {GetRequestById(id)}
    /\ UNCHANGED <<tier_one_addresses, tier_two_addresses, delay, unlock_block, special_vars>>
 
CancelRequest(address1, id) == 
    /\ Tick
    /\ previous_command' = (<<"cancel_request", address1, id>>) 
    /\ address1 \in tier_one_addresses
    /\ id \in GetIds
    /\ requests' = requests \ {GetRequestById(id)}
    /\ UNCHANGED <<balance, tier_one_addresses, tier_two_addresses, delay, unlock_block, special_vars>>

CancelAllRequests(address1) ==
    /\ Tick
    /\ previous_command' =(<<"cancel_all_requests", address1>>) 
    /\ address1 \in tier_one_addresses
    /\ requests' = {}
    /\ UNCHANGED <<balance, tier_one_addresses, tier_two_addresses, delay, unlock_block, special_vars>>

CancelSelfRequest(address2, id) ==
    /\ Tick
    /\ previous_command' = (<<"cancel_self_request", address2, id>>) 
    /\ address2 \in tier_two_addresses
    /\ id \in GetIds
    /\ GetRequestById(id)[4] = address2
    /\ requests' = requests \ {GetRequestById(id)}
    /\ UNCHANGED <<balance, tier_one_addresses, tier_two_addresses, delay, unlock_block, special_vars>>

Lock(address1, new_unlock_block) ==
    /\ Tick
    /\ previous_command' = (<<"lock", address1>>) 
    /\ address1 \in tier_one_addresses
    /\ new_unlock_block > unlock_block
    /\ new_unlock_block > block_number
    /\ unlock_block' = new_unlock_block
    /\ UNCHANGED <<balance, tier_one_addresses, tier_two_addresses, delay, requests, special_vars>>
    
AddTierOneAddress(address1, new_address1) == 
    /\ Tick
    /\ previous_command' = (<<"add_tier_one", address1>>) 
    /\ address1 \in tier_one_addresses
    /\ new_address1 \notin tier_one_addresses
    /\ new_address1 \notin tier_two_addresses
    /\ tier_one_addresses' = tier_one_addresses \union {new_address1}
    /\ owner_known_addresses' = owner_known_addresses \union {new_address1}
    /\ UNCHANGED <<balance, tier_two_addresses, delay, unlock_block, requests, adversary_known_addresses>>

AddTierTwoAddress(address1, new_address2) == 
    /\ Tick
    /\ previous_command' = (<<"add_tier_two", address1>>) 
    /\ address1 \in tier_one_addresses
    /\ new_address2 \notin tier_one_addresses
    /\ new_address2 \notin tier_two_addresses
    /\ tier_two_addresses' = tier_two_addresses \union {new_address2}
    /\ owner_known_addresses' = owner_known_addresses \union {new_address2}
    /\ UNCHANGED <<balance, tier_one_addresses, delay, unlock_block, requests, adversary_known_addresses>>

RemoveTierTwoAddress(address1, remove_address2) == 
    /\ Tick
    /\ previous_command' = (<<"remove_tier_two", address1>>) 
    /\ address1 \in tier_one_addresses
    /\ remove_address2 \in tier_two_addresses
    /\ tier_two_addresses' = tier_two_addresses \ {remove_address2}
    /\ owner_known_addresses' = owner_known_addresses \ {remove_address2}
    /\ requests' = FilterNotByInitiator(remove_address2)
    /\ UNCHANGED <<balance, tier_one_addresses, delay, unlock_block, adversary_known_addresses>>

OwnerAction ==
    \/ \E amount \in MONEY: 
        Deposit(amount)
    \/ \E <<address2, amount, recipient>> \in owner_known_addresses \X MONEY \X (NETWORK_ADDRESSES \ {ADVERSARY_ADDRESS}):
        Request(address2, amount, recipient)
    \/ \E id \in REQUEST_IDS: 
        Withdraw(id) 
    \/ \E <<address1, id>> \in owner_known_addresses \X REQUEST_IDS: 
        CancelRequest(address1, id)
    \/ \E address1 \in owner_known_addresses: 
        CancelAllRequests(address1) 
    \/ \E <<address2, id>> \in owner_known_addresses \X REQUEST_IDS: 
        CancelSelfRequest(address2, id) 
    \/ \E <<address1, new_unlock_block>> \in owner_known_addresses \X (0..MAX_BLOCK_NUMBER): 
        Lock(address1, new_unlock_block)
    \/ \E <<address1, new_address1>> \in owner_known_addresses \X ADDRESSES: 
        AddTierOneAddress(address1, new_address1)
    \/ \E <<address1, new_address2>> \in owner_known_addresses \X ADDRESSES: 
        AddTierTwoAddress(address1, new_address2)
    \/ \E <<address1, remove_address2>> \in owner_known_addresses \X ADDRESSES: 
        RemoveTierTwoAddress(address1, remove_address2) 

KeyLoss(address) ==
    /\ SIMULATE_EVENT = "key_loss"
    /\ Cardinality(owner_known_addresses) > 1
    /\ address \in owner_known_addresses
    /\ previous_command' = <<"key_loss">>
    /\ owner_known_addresses' = owner_known_addresses \ {address}
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests, adversary_known_addresses>>

AddTierTwoAddressForAdversary(address1, new_address2) == 
    /\ Tick
    /\ previous_command' = (<<"add_tier_two", address1>>) 
    /\ address1 \in tier_one_addresses
    /\ new_address2 \notin tier_one_addresses
    /\ new_address2 \notin tier_two_addresses
    /\ tier_two_addresses' = tier_two_addresses \union {new_address2}
    /\ adversary_known_addresses' = adversary_known_addresses \union {new_address2}
    /\ UNCHANGED <<balance, tier_one_addresses, delay, unlock_block, requests, owner_known_addresses>>

TypeOneAttack(address) ==
    /\ SIMULATE_EVENT = "type_one_attack"
    /\ address \in tier_one_addresses
    /\ previous_command' = <<"type_one_attack">>
    /\ adversary_known_addresses' = adversary_known_addresses \union {address}
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests, owner_known_addresses>>

TypeTwoAttack(address) ==
    /\ SIMULATE_EVENT = "type_two_attack"
    /\ address \in tier_two_addresses
    /\ previous_command' = <<"type_two_attack">>
    /\ adversary_known_addresses' = adversary_known_addresses \union {address}
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests, owner_known_addresses>>

TypeOneAttackDefence ==
    /\ SIMULATE_EVENT = "type_one_attack"
    /\ balance[ADVERSARY_ADDRESS] = 0
    /\ \E req \in requests: 
        req[5] = ADVERSARY_ADDRESS
    /\ \E address1 \in ADDRESSES:
        Lock(address1, MAX_BLOCK_NUMBER + 1)

AdversaryAction == 
    \/ \E <<address2, amount, recipient>> \in adversary_known_addresses \X MONEY \X NETWORK_ADDRESSES:
        Request(address2, amount, recipient)
    \/ \E id \in REQUEST_IDS: 
        Withdraw(id) 
    \/ \E <<address1, id>> \in adversary_known_addresses \X REQUEST_IDS: 
        CancelRequest(address1, id)
    \/ \E address1 \in adversary_known_addresses: 
        CancelAllRequests(address1) 
    \/ \E <<address2, id>> \in adversary_known_addresses \X REQUEST_IDS: 
        CancelSelfRequest(address2, id) 
    \/ \E <<address1, new_address2>> \in adversary_known_addresses \X ADDRESSES: 
        AddTierTwoAddress(address1, new_address2)
    \/ \E <<address1, remove_address2>> \in adversary_known_addresses \X ADDRESSES: 
        RemoveTierTwoAddress(address1, remove_address2) 

EnvironmentAction ==
    \/ \E address \in ADDRESSES: 
        KeyLoss(address)
    \/ \E address \in ADDRESSES: 
        TypeOneAttack(address)
    \/ \E address \in ADDRESSES: 
        TypeTwoAttack(address)

Next ==
    \/ OwnerAction 
    \/ AdversaryAction
    \/ EnvironmentAction

Spec == Init /\ [][Next]_vars

\* WF = weak fairness

Fairness ==
    /\ SF_vars(TypeOneAttackDefence)
    \* /\ \A s \in ADDRESSES: WF_vars(GetReimbursed(s))
    \* /\ WF_vars(Tick)
    

FairSpec == Spec /\ Fairness

--------------------------------------
\* PROPERTIES

RecoversKeyLoss ==
    TRUE
RecoversTypeOneAttack == 
    [](SIMULATE_EVENT = "type_one_attack" => balance[ADVERSARY_ADDRESS] = 0)
RecoversTypeTwoAttack ==
    [](SIMULATE_EVENT = "type_two_attack" => balance[ADVERSARY_ADDRESS] = 0)

\* 1. Base layer
\* 1.1.
CannotWithdrawBeforeDelay ==
    [][previous_command'[1] = "withdraw" => \A r \in requests: (r[1] = previous_command'[2] => r[3] + delay <= block_number)]_previous_command
\* 1.2.
\* TierOneCanCancelAnyRequestAnyTime ==
\*     []((requests /= {} /\ block_number < MAX_BLOCK_NUMBER) => LET b == block_number IN 
\*         <>(
\*             /\ block_number = b + 1                    \* _<<tier_one_addresses, requests>>

\*             /\ previous_command[1] = "cancel_request"
\*             /\ previous_command[2] \in tier_one_addresses))
TierOneCanCancelAnyRequestAnyTime ==
    []((requests /= {} /\ block_number < MAX_BLOCK_NUMBER) => 
        LET b == block_number IN 
            (\A r \in request_type:
                r \in requests =>
                (~[](
                    /\ block_number = b + 1
                    /\ previous_command[1] = "cancel_request"
                    /\ previous_command[2] \in tier_one_addresses
                    /\ previous_command[3] = r[1]))))
\* 1.3.
CannotChangeDelay ==
    \E d \in 0..MAX_BLOCK_NUMBER: [](delay = d)
\* 1.4.
CannotRemoveTierOneAddress == 
    [][\A a \in ADDRESSES: a \in tier_one_addresses => a \in tier_one_addresses']_<<tier_one_addresses>>
\* 1.5.
CannotBeDestroyedUnlessEmpty ==
    <>[](balance[OWNER_ADDRESS] = 0)

\* 2. Key separation layer
\* 2.1.
TierOneAndTwoSeparated == 
    [](tier_one_addresses \intersect  tier_two_addresses = {})
\* 2.2.
OnlyTierOneCanAddTierOne ==
    [][previous_command'[1] = "add_tier_one" => previous_command'[2] \in tier_one_addresses]_previous_command
\* 2.3.
OnlyTierTwoCanRequest ==
    [][previous_command'[1] = "request" => previous_command'[2] \in tier_two_addresses]_previous_command
\* 2.4.
TierTwoCanCancelOnlyItselfRequests ==
    [][previous_command'[1] = "cancel_self_request" => 
            /\ previous_command'[2] \in tier_two_addresses 
            /\ GetRequestById(previous_command'[3])[4] = previous_command'[2]]_previous_command
    


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
    [](balance[OWNER_ADDRESS] >= Sum)
\* 4.2.
CannotSendMoneyToItself ==
    [](\A r \in requests: r[5] /= OWNER_ADDRESS)
\* 4.3.
CannotSendMoneyToZero ==
    [](\A r \in requests: r[5] /= 0)
\* 4.4.
RemovingTierTwoRemovesItsRequests ==
    [][previous_command'[1] = "remove_tier_two" => {req \in requests': req[4] /= previous_command'[2]} = requests']_<<previous_command, requests>>




--------------------------------------

ADDRESSES_const == 0..4
NETWORK_ADDRESSES_const == 1..3
MONEY_const == 1..1
REQUEST_IDS_const == 0..MAX_BLOCK_NUMBER

====