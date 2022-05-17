# Прект по матлогу

### Задача:

Построить TLA+ модель для смарт-контракта [Phoenix Vault, описанного в статье Phoenix: A Formally Verified Regenerating Vault (2021)](https://arxiv.org/abs/2106.01240) за авторством Uri Kirstein, Shelly Grossman, Michael Mirkin, James Wilcox, Ittay Eyal, Mooly Sagiv

## Модель

### Части контракта

- Balance F
- Delay D
- Tier-one addresses T1
- Tier-two addresses T2
- Unlock time U
- Requests R


### Действия

- Deposit
- Request
- Withdraw
- Cancel request
- Cancel all requests
- Cancel self request
- Lock
- Add a T1 address
- Add a T2 address 
- Remove a T2 address


### Свойства

1. Base layer

    1.1 Requests cannot be withdrawn unless they have been kept in Phoenix’s records for an amount of time equal or greater than Phoenix’s delay.

    1.2 A tier-one address can cancel any request at any time.

    1.3 Phoenix’s delay can never change.

    1.4 There is no way to remove a tier-one address.

    1.5 Phoenix cannot be destroyed unless it is empty.

2. Key separation layer

    2.1 An address cannot have both tier-one and tier-two privileges.

    2.2 Tier-one addresses can only be added by a tier-one address.

    2.3 Only a tier-two address can spend money.

    2.4 A tier-two address can only remove self-initiated requests.

3. Recovery layer

    3.1 Money cannot leave Phoenix while it is locked.

    3.2 The unlock time can only be postponed.

    3.3 Only tier-one addresses can lock Phoenix.

    3.4 Only tier-one addresses can remove tier-two addresses.

    3.5 Only tier-one addresses can add tier-two addresses.

4. Tier-one minimization layer

    4.1 There are always enough funds in Phoenix to pay for all requests.

    4.2 Phoenix cannot send money to itself.

    4.3 Phoenix cannot send money to the zero address.

    4.4 Removing a tier-two address from Phoenix also removes all requests initiated bythat address

