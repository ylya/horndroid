package com.horndroid.exceptions;

/**
 * This exception is thrown when report formatting or printing fails
 *
 * @author Sharmeen
 */
public class ReportWritingException extends Exception {
    public ReportWritingException(String message) {
        super(message);
    }

    public ReportWritingException(String s, Throwable e) {
        super(s, e);
    }
}
