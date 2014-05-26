package com.intellij.codeInspection.bytecodeAnalysis;


import org.objectweb.asm.ClassReader;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.Enumeration;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

interface Source {
    void process(Processor processor);
}

final class JarFileSource implements Source {
    final File file;

    JarFileSource(File file) {
        this.file = file;
    }

    @Override
    public void process(Processor processor) {
        try {
            JarFile jarFile = new JarFile(file);
            Enumeration<JarEntry> entries = jarFile.entries();
            while (entries.hasMoreElements()) {
                JarEntry entry = entries.nextElement();
                if (entry.getName().endsWith(".class")) {
                    InputStream is = jarFile.getInputStream(entry);
                    try {
                        processor.processClass(new ClassReader(is));
                    } finally {
                        is.close();
                    }
                }
            }
        } catch (IOException e) {
            // TODO
        }
    }
}

final class ClassSource implements Source {
    final Class<?> aClass;

    ClassSource(Class<?> aClass) {
        this.aClass = aClass;
    }

    @Override
    public void process(Processor processor) {
        try {
            processor.processClass(new ClassReader(aClass.getCanonicalName()));
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}


interface Processor {
    void processClass(ClassReader classReader);
}