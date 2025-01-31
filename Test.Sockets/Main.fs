open System
open System.Net
open System.Net.Sockets
open System.Text

[<EntryPoint>]
let main args =

    // Параметры подключения (можно изменить при необходимости)
    let host = "127.0.0.1"  // или "localhost"
    let port = 35100

    printfn "Подключение к %s:%i..." host port

    // Создаем TCP-клиент и подключаемся к удалённому хосту
    use client = new TcpClient()
    client.Connect(host, port)

    // Получаем сетевой поток для записи
    use stream = client.GetStream()
    printfn "Подключено. Введите строки для отправки (Ctrl+C для выхода)."

    // Бесконечный цикл чтения строк с консоли и отправки их в сокет
    let rec sendLoop () =
        printf "> "
        let line = Console.ReadLine()
        match line with
        | null | "" ->
            // Если ввели пустую строку или EOF (null),
            // при желании можно завершить работу или пропустить итерацию.
            // В примере завершим отправку.
            printfn "Завершение..."
            ()
        | text ->
            // Преобразуем строку в байты и отправляем.
            // Добавляем перевод строки.
            let bytes = Encoding.UTF8.GetBytes(text + Environment.NewLine)
            stream.Write(bytes, 0, bytes.Length)
            stream.Flush()
            // Переходим к следующему циклу
            sendLoop()

    sendLoop()

    0 // код возврата из приложения