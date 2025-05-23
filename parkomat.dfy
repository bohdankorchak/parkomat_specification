module ParkomatModule {
  // Тип талону містить унікальний номер талону, час видачі та номер авто.
  datatype Ticket = Ticket(ticketId: int, issueTime: int, carNumber: string)

  class Parkomat {
    const freeMinutes: int := 30
    const costPerMinute: int := 1

    var paid: bool
    var nextTicketId: int
    var tickets: map<string, Ticket>
    var ticketsById: map<int, Ticket>

    constructor ()
      ensures paid == false && nextTicketId == 1 && tickets == map [] && ticketsById == map []
    {
      paid := false;
      nextTicketId := 1;
      tickets := map [];
      ticketsById := map [];
    }

    // Метод сканування номера авто.
    method ScanCarNumber(inputCarNumber: string) returns (scanned: string)
      ensures scanned == inputCarNumber
    {
      scanned := inputCarNumber;
    }

    // Метод створення талону.
    method PressButtonGetTicket(currentTime: int, inputCarNumber: string) returns (ticket: Ticket)
      requires currentTime >= 0
      modifies this
      ensures ticket.issueTime == currentTime && ticket.carNumber == inputCarNumber
      ensures inputCarNumber in tickets && tickets[inputCarNumber] == ticket
      ensures ticket.ticketId in ticketsById && ticketsById[ticket.ticketId] == ticket
    {
      var carNumber := ScanCarNumber(inputCarNumber);
      ticket := Ticket(nextTicketId, currentTime, carNumber);
      tickets := tickets[carNumber := ticket];
      ticketsById := ticketsById[ticket.ticketId := ticket];
      nextTicketId := nextTicketId + 1;
    }

    // Функція розрахунку плати за талоном.
    function FeeFromTicket(ticket: Ticket, exitTime: int) : int {
      if exitTime - ticket.issueTime <= freeMinutes then 0
      else (exitTime - ticket.issueTime - freeMinutes) * costPerMinute
    }

    // загальна функція розрахунку плати:
    // Якщо для заданого номера авто існує талон, використовуємо його, інакше – талон за номером талону.
    function CalculateFeeFallbackF(inputCarNumber: string, inputTicketId: int, exitTime: int) : int
      reads this
      requires inputCarNumber in tickets || inputTicketId in ticketsById
    {
      if inputCarNumber in tickets then 
        FeeFromTicket(tickets[inputCarNumber], exitTime)
      else if inputTicketId in ticketsById then
        FeeFromTicket(ticketsById[inputTicketId], exitTime)
      else
        0
    }

    // Метод прийому оплати за допомогою картки.
    method AcceptCardPayment(amount: int, fee: int) returns (success: bool, change: int)
      requires fee >= 0
      modifies this
      ensures success <==> amount >= fee
      ensures change == amount - fee <==> amount >= fee
    {
      if amount >= fee {
        paid := true;
        success := true;
        change := amount - fee;
      } else {
        success := false;
        change := 0;
      }
    }

    // Метод прийому оплати готівкою.
    method AcceptCashPayment(amount: int, fee: int) returns (success: bool, change: int)
      requires fee >= 0
      modifies this
      ensures success <==> amount >= fee
      ensures change == amount - fee <==> amount >= fee
    {
      if amount >= fee {
        paid := true;
        success := true;
        change := amount - fee;
      } else {
        success := false;
        change := 0;
      }
    }

    // Метод відкриття шлагбауму.
    method VerifyOpenBarrier(condition: bool) returns (barrierOpened: bool)
      ensures barrierOpened <==> condition
    {
      if condition {
          barrierOpened := true;
      } else {
          barrierOpened := false;
      }
    }
  }

method Main() {
    var parkomat := new Parkomat();
    var ticket := parkomat.PressButtonGetTicket(100, "ABC123");
    var barrierOpened: bool;

    var exitTime := 150; // Паркування 50 хвилин: оплата = (50 - 30) * 1 = 20
    var fee := parkomat.FeeFromTicket(ticket, exitTime);
    
    barrierOpened := parkomat.VerifyOpenBarrier(fee == 0);
  
    assert fee == 20;
    assert !barrierOpened;

    var paymentSuccess: bool;
    var change: int;
    
    // Приклад використання методу AcceptCardPayment:
    // Якщо fee = 20, а на карті 5, то оплата не успішна.
    paymentSuccess, change := parkomat.AcceptCardPayment(2, fee);
    assert !paymentSuccess;

    barrierOpened := parkomat.VerifyOpenBarrier(paymentSuccess);
    assert !barrierOpened;

    // Приклад використання методу AcceptCashPayment:
    // Якщо fee = 20, а внесено 50, то change має бути 30.
    paymentSuccess, change := parkomat.AcceptCashPayment(50, fee);
    assert change == 50 - fee;
    assert paymentSuccess;

    barrierOpened := parkomat.VerifyOpenBarrier(paymentSuccess);
    assert barrierOpened;
    
  }
}
